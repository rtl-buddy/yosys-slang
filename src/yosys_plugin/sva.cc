//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// clang-format off
#include <algorithm>
#include <string>
#include <vector>
#include <optional>
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/SemanticFacts.h"
#include "kernel/rtlil.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/ScopeGuard.h"

#include "slang_frontend.h"
#include "statements.h"
#include "diag.h"

namespace slang_frontend {

// SVA sequences and implication (rtl-buddy fork). This portion was written by
// Louis-Emile Ploix "mndstrmr" (c) 2025, ISC licence; brought onto slang head by Mel Young
// 2026 (rtl-buddy/yosys-slang 297f58f), with the property evaluated in SVA context
// (273a7eb); ported onto the ir layer for sv-elab 2cfcfbe. A sequence is a set of paths, each
// an ending condition and the number of cycles it looks back (`start`), built from $ff delay
// lines on the formal global clock.

static RTLIL::SigSpec sva_past(EvalContext &eval, RTLIL::SigSpec sig, int time, RTLIL::Const init)
{
	auto *canvas = eval.netlist.backend->canvas;
	for (int i = 0; i < time; i++) {
		auto next = canvas->addWire(eval.netlist.backend->new_id(), sig.size());
		next->attributes[ID::init] = init;
		canvas->addFf(eval.netlist.backend->new_id(), sig, next);
		sig = next;
	}
	return sig;
}

static RTLIL::SigSpec sig_of(ir::Net n) { return RTLIL::SigSpec(ir::Value(n)); }

struct AssertionMatch {
	EvalContext &eval;
	RTLIL::SigSpec sig;
	int start;

	AssertionMatch(EvalContext &eval_, RTLIL::SigSpec sig_) : eval(eval_), sig(sig_), start(0) {}

private:
	AssertionMatch(EvalContext &eval_, RTLIL::SigSpec sig_, int start_) : eval(eval_), sig(sig_), start(start_) {}

public:
	AssertionMatch(const AssertionMatch &other) = default;
	AssertionMatch &operator=(const AssertionMatch &other)
	{
		sig = other.sig;
		start = other.start;
		return *this;
	}

	AssertionMatch shift(int time) const
	{
		if (sig.is_fully_const())
			return {eval, sig, start + time};
		return {eval, sva_past(eval, sig, time, RTLIL::State::Sx), start + time};
	}

	AssertionMatch operator||(const AssertionMatch &other) const
	{
		int s = std::max(other.start, start);
		if (sig.is_fully_const() && sig.as_bool()) return {eval, RTLIL::SigSpec(true), s};
		if (sig.is_fully_const() && !sig.as_bool()) return {eval, other.sig, s};
		if (other.sig.is_fully_const() && other.sig.as_bool()) return {eval, RTLIL::SigSpec(true), s};
		if (other.sig.is_fully_const() && !other.sig.as_bool()) return {eval, sig, s};
		return {eval, sig_of(eval.netlist.LogicOr(sig, other.sig)), s};
	}

	AssertionMatch operator&&(const AssertionMatch &other) const
	{
		int s = std::max(other.start, start);
		if (sig.is_fully_const() && sig.as_bool()) return {eval, other.sig, s};
		if (sig.is_fully_const() && !sig.as_bool()) return {eval, RTLIL::SigSpec(false), s};
		if (other.sig.is_fully_const() && other.sig.as_bool()) return {eval, sig, s};
		if (other.sig.is_fully_const() && !other.sig.as_bool()) return {eval, RTLIL::SigSpec(false), s};
		return {eval, sig_of(eval.netlist.LogicAnd(sig, other.sig)), s};
	}

	AssertionMatch operator!() const
	{
		if (sig.is_fully_const()) return {eval, RTLIL::SigSpec(!sig.as_bool()), start};
		return {eval, sig_of(eval.netlist.LogicNot(sig)), start};
	}
};

static std::vector<AssertionMatch> compress_paths(std::vector<AssertionMatch> paths)
{
	std::sort(paths.begin(), paths.end(),
			  [](const AssertionMatch &a, const AssertionMatch &b) { return a.start > b.start; });

	std::vector<AssertionMatch> grouped;
	std::optional<AssertionMatch> group;
	int time = -1;
	for (auto &path : paths) {
		if (path.start != time) {
			if (group.has_value()) grouped.push_back(group.value());
			time = path.start;
			group.emplace(path);
		} else {
			group.emplace(group.value() || path);
		}
	}
	if (group.has_value()) grouped.push_back(group.value());
	return grouped;
}

static std::vector<AssertionMatch> not_vec(std::vector<AssertionMatch> in)
{
	if (in.empty()) return {};
	AssertionMatch collapsed = in[0];
	for (size_t i = 1; i < in.size(); i++) {
		if (collapsed.start >= in[i].start)
			collapsed = in[i].shift(collapsed.start - in[i].start) || collapsed;
		else
			collapsed = collapsed.shift(in[i].start - collapsed.start) || in[i];
	}
	return {!collapsed};
}

static std::vector<AssertionMatch> seq_vec(std::vector<AssertionMatch> a, int min, int max, std::vector<AssertionMatch> b)
{
	std::vector<AssertionMatch> new_own_paths;
	for (auto &path : a)
		for (int offset = min; offset <= max; offset++)
			for (auto &inner : b)
				new_own_paths.push_back(path.shift(offset + inner.start) && inner);
	return compress_paths(new_own_paths);
}

static slang::SourceLocation expr_loc(const ast::AssertionExpr &expr)
{
	return expr.syntax ? expr.syntax->sourceRange().start() : slang::SourceLocation::NoLocation;
}

// Empty indicates an error (a diagnostic has been issued)
static std::vector<AssertionMatch> synthesizeAssertionExpr(EvalContext &eval, const ast::AssertionExpr &expr)
{
	switch (expr.kind) {
	case ast::AssertionExprKind::Invalid:
		log_abort();
	case ast::AssertionExprKind::Simple: {
		const auto &simple = expr.as<ast::SimpleAssertionExpr>();
		// Upstream's check, kept: a repetition must not be read as a single match
		if (simple.repetition.has_value()) {
			eval.netlist.add_diag(diag::RepetitionsUnsupported, expr.syntax ? expr.syntax->sourceRange() : slang::SourceRange());
			return {};
		}
		if (simple.isNullExpr)
			return {{eval, RTLIL::SigSpec(false)}};
		return {{eval, RTLIL::SigSpec(eval.sva(simple.expr))}};
	}
	case ast::AssertionExprKind::SequenceConcat: {
		const auto &sequence = expr.as<ast::SequenceConcatExpr>();
		std::vector<AssertionMatch> own_paths;
		own_paths.push_back({eval, RTLIL::SigSpec(true)});
		for (size_t i = 0; i < sequence.elements.size(); i++) {
			auto inner_paths = synthesizeAssertionExpr(eval, *sequence.elements[i].sequence);
			if (inner_paths.empty()) return {};
			auto delay = sequence.elements[i].delay;
			if (!delay.max.has_value()) {
				eval.netlist.add_diag(diag::AssertionUnsupported, expr_loc(expr));
				return {};
			}
			own_paths = seq_vec(own_paths, delay.min, delay.max.value(), inner_paths);
		}
		return own_paths;
	}
	case ast::AssertionExprKind::Unary: {
		const auto &uop = expr.as<ast::UnaryAssertionExpr>();
		switch (uop.op) {
		case ast::UnaryAssertionOperator::Not:
			return not_vec(synthesizeAssertionExpr(eval, uop.expr));
		default:
			eval.netlist.add_diag(diag::AssertionUnsupported, expr_loc(expr));
			return {};
		}
	}
	case ast::AssertionExprKind::Binary: {
		const auto &biop = expr.as<ast::BinaryAssertionExpr>();
		auto left = synthesizeAssertionExpr(eval, biop.left);
		auto right = synthesizeAssertionExpr(eval, biop.right);
		if (left.empty() || right.empty()) return {}; // propagate errors

		switch (biop.op) {
		case ast::BinaryAssertionOperator::And: {
			// te1 and te2 matches if both match; it ends when the later one ends
			std::vector<AssertionMatch> results;
			for (auto &a : left)
				for (auto &b : right) {
					if (a.start >= b.start)
						results.push_back(b.shift(a.start - b.start) && a);
					else
						results.push_back(a.shift(b.start - a.start) && b);
				}
			return compress_paths(results);
		}
		case ast::BinaryAssertionOperator::Or:
			left.insert(left.end(), right.begin(), right.end());
			return left;
		case ast::BinaryAssertionOperator::OverlappedImplication:
			return not_vec(seq_vec(left, 0, 0, not_vec(right)));
		case ast::BinaryAssertionOperator::NonOverlappedImplication:
			return not_vec(seq_vec(left, 1, 1, not_vec(right)));
		default:
			eval.netlist.add_diag(diag::AssertionUnsupported, expr_loc(expr));
			return {};
		}
	}
	case ast::AssertionExprKind::Clocking:
		// Clocking is stripped at the top; inner clocking uses the same global clock
		return synthesizeAssertionExpr(eval, expr.as<ast::ClockingAssertionExpr>().expr);
	case ast::AssertionExprKind::DisableIff: {
		const auto &disableiff = expr.as<ast::DisableIffAssertionExpr>();
		AssertionMatch disable{eval, RTLIL::SigSpec(eval.sva(disableiff.condition))};
		auto inner = synthesizeAssertionExpr(eval, disableiff.expr);
		std::vector<AssertionMatch> disables;
		disables.push_back(disable);
		for (size_t i = 0; i < inner.size(); i++) {
			std::optional<AssertionMatch> this_disables;
			for (int t = 0; t <= inner[i].start; t++) {
				while ((int) disables.size() <= t)
					disables.push_back(disables.back().shift(1));
				if (this_disables.has_value())
					this_disables.emplace(this_disables.value() || disables[t]);
				else
					this_disables.emplace(disables[t]);
			}
			if (this_disables.has_value())
				inner[i] = this_disables.value() || inner[i];
		}
		return inner;
	}
	default:
		eval.netlist.add_diag(diag::AssertionUnsupported, expr_loc(expr));
		return {};
	}
}

static RTLIL::SigSpec evalAssertion(EvalContext &eval, const ast::AssertionExpr &assertion)
{
	auto paths = synthesizeAssertionExpr(eval, assertion);
	if (paths.empty()) return RTLIL::SigSpec(false); // a diagnostic has been issued

	auto sig = paths[0];
	for (size_t i = 1; i < paths.size(); i++) sig = sig || paths[i];

	// The check is held off until every path's look-back is inside the trace
	auto init_escape = sva_past(eval, RTLIL::SigSpec(false), sig.start, RTLIL::Const(RTLIL::State::S1, 1));
	return sig_of(eval.netlist.LogicOr(sig.sig, init_escape));
}

// Process a 'concurrent assertion'
//
// Any top level clocking expressions have been stripped. Clocking is part
// of the created procedural context.
void process_sva_property(const ast::ConcurrentAssertionStatement &statement,
						  const ast::StatementBlockSymbol *block,
						  ProceduralContext &procedural, const ast::AssertionExpr &top_expr)
{
	auto &netlist = procedural.netlist;

	const ast::AssertionExpr *expr = &top_expr;
	slang::SourceRange source_range = expr->syntax ? expr->syntax->sourceRange() : statement.sourceRange;

	// Extract disable iff condition if present; the extracted switch
	// needs to live until the end of the function to be picked up
	// by set_effects_trigger
	std::optional<SwitchHelper> switch_;
	auto guard = slang::ScopeGuard([&] {
		if (switch_.has_value()) {
			switch_->exit_branch();
			switch_->finish(netlist);
		}
	});
	if (ast::DisableIffAssertionExpr::isKind(expr->kind)) {
		auto &disable = expr->as<ast::DisableIffAssertionExpr>();
		switch_.emplace(procedural, netlist.ReduceBool(procedural.eval.sva(disable.condition)));
		switch_->enter_branch({ir::S0});
		expr = &disable.expr;
		source_range = expr->syntax ? expr->syntax->sourceRange() : statement.sourceRange;
	}

	(void) source_range;
	// Evaluate the property with its disable iff, if any (top_expr), not only the stripped
	// expr: the switch above disables on the condition's current value, but an attempt is
	// disabled if the condition holds at any cycle of it (IEEE 1800-2017 16.12), which
	// synthesizeAssertionExpr's DisableIff case encodes over the property's look-back.
	RTLIL::SigSpec result = evalAssertion(procedural.eval, top_expr);

	std::string flavor;
	switch (statement.assertionKind) {
	case ast::AssertionKind::Assert:        flavor = "assert"; break;
	case ast::AssertionKind::Assume:        flavor = "assume"; break;
	case ast::AssertionKind::CoverProperty: flavor = "cover"; break;
	default:                                netlist.add_diag(diag::AssertionUnsupported, statement.sourceRange); return;
	}

	std::string cell_name;

	if (block && unwrap_statement(block->tryGetStatement()) == &statement && !block->name.empty()) {
		// If we are the sole statement in a block, use the block's label
		cell_name = netlist.id(*block);
	} else {
		cell_name = netlist.backend->new_id();
	}

	ir::Net a = netlist.ReduceBool(result);

	auto cell = netlist.backend->canvas->addCell(std::move(cell_name), ID($check));
	procedural.set_effects_trigger(cell);
	cell->setParam(ID::FLAVOR, flavor);
	cell->setParam(ID::FORMAT, std::string(""));
	cell->setParam(ID::ARGS_WIDTH, 0);
	cell->setParam(ID::PRIORITY, --procedural.effects_priority);
	cell->setPort(ID::ARGS, {});
	cell->setPort(ID::A, {a});
	transfer_attrs(netlist, statement, cell);
}

void process_freestanding_sva_property(NetlistContext &netlist,
									   const ast::ConcurrentAssertionStatement &statement,
						  			   const ast::StatementBlockSymbol *block)
{
	const ast::AssertionExpr &spec = statement.propertySpec;

	if (ast::ClockingAssertionExpr::isKind(spec.kind)) {
		// Need to strip clocking
		const auto &clocking_expr = spec.as<ast::ClockingAssertionExpr>();
		const auto &clocking = clocking_expr.clocking;

		if (!ast::SignalEventControl::isKind(clocking.kind)) {
			netlist.add_diag(diag::UnsupportedSVAFeature, clocking.sourceRange);
			return;
		}

		const auto &signal_event = clocking.as<ast::SignalEventControl>();

		ProcessTiming timing(ProcessTiming::EdgeTriggered);
		switch (signal_event.edge) {
		case ast::EdgeKind::None:
			netlist.add_diag(diag::SVAClockingRequiresEdge, signal_event.sourceRange);
			return;

		case ast::EdgeKind::PosEdge:
		case ast::EdgeKind::NegEdge:
			timing.triggers.push_back(ProcessTiming::Sensitivity {
				.signal = netlist.eval(signal_event.expr).as_net(),
				.edge_polarity = (signal_event.edge == ast::EdgeKind::PosEdge),
				.ast_node = &clocking
			});
			break;

		case ast::EdgeKind::BothEdges:
			netlist.add_diag(diag::BothEdgesUnsupported, signal_event.sourceRange);
			return;
		}

		if (signal_event.iffCondition) {
			// TODO
			netlist.add_diag(diag::IffUnsupported, signal_event.iffCondition->sourceRange);
		}

		ProceduralContext procedure(netlist, timing);
		process_sva_property(statement, block, procedure, clocking_expr.expr);

		RTLIL::Process *rtlil_proc = netlist.backend->canvas->addProcess(netlist.backend->new_id());
		transfer_attrs(netlist, statement, rtlil_proc);
#ifndef SLANG_MUX_LOWERING
		procedure.copy_case_tree_into(rtlil_proc->root_case);
#endif
	} else {
		// No clocking
		ProceduralContext procedure(netlist, ProcessTiming::implicit);
		process_sva_property(statement, block, procedure, spec);

		RTLIL::Process *rtlil_proc = netlist.backend->canvas->addProcess(netlist.backend->new_id());
		transfer_attrs(netlist, statement, rtlil_proc);
#ifndef SLANG_MUX_LOWERING
		procedure.copy_case_tree_into(rtlil_proc->root_case);
#endif
	}
}

};
