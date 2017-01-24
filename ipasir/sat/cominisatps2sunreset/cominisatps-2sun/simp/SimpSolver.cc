/***********************************************************************************[SimpSolver.cc]
MiniSat -- Copyright (c) 2006,      Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "mtl/Sort.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "SIMP";

static BoolOption   opt_use_asymm        (_cat, "asymm",        "Shrink clauses by asymmetric branching.", false);
static BoolOption   opt_use_rcheck       (_cat, "rcheck",       "Check if a clause is already implied. (costly)", false);
static BoolOption   opt_use_elim         (_cat, "elim",         "Perform variable elimination.", true);
static IntOption    opt_grow             (_cat, "grow",         "Allow a variable elimination step to grow by a number of clauses.", 0);
static IntOption    opt_clause_lim       (_cat, "cl-lim",       "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit", 20,   IntRange(-1, INT32_MAX));
static IntOption    opt_subsumption_lim  (_cat, "sub-lim",      "Do not check if subsumption against a clause larger than this. -1 means no limit.", 1000, IntRange(-1, INT32_MAX));
static DoubleOption opt_simp_garbage_frac(_cat, "simp-gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered during simplification.",  0.5, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    grow               (opt_grow)
  , clause_lim         (opt_clause_lim)
  , subsumption_lim    (opt_subsumption_lim)
  , simp_garbage_frac  (opt_simp_garbage_frac)
  , use_asymm          (opt_use_asymm)
  , use_rcheck         (opt_use_rcheck)
  , use_elim           (opt_use_elim)
  , merges             (0)
  , asymm_lits         (0)
  , eliminated_vars    (0)
  , use_simplification (true)
  , occurs             (ClauseDeleted(ca))
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
  , n_touched          (0)

  , elim_heap_incr     (ElimIncrLt(elim_order))
  , elim_order_cnt     (1)
{
    vec<Lit> dummy(1,lit_Undef);
    ca.extra_clause_field = true; // NOTE: must happen before allocating the dummy clause below.
    bwdsub_tmpunit        = ca.alloc(dummy);
    remove_satisfied      = false;
}


SimpSolver::~SimpSolver()
{
}


Var SimpSolver::newVar(bool sign, bool dvar) {
    Var v = Solver::newVar(sign, dvar);

    frozen      .push((char)false);
    elim_clauses.push();
    elim_clauses.push();
    to_resolve  .push();
    to_resolve  .push();
    elim_order  .push(0);

    if (use_simplification){
        n_occ     .push(0);
        n_occ     .push(0);
        occurs    .init(v);
        touched   .push(0);
        elim_heap .insert(v);
    }
    return v; }



lbool SimpSolver::solve_(bool do_simp, bool turn_off_simp)
{
//printf("c assumptions:");
//for (int i = 0; i < assumptions.size(); i++) printf(" %s%d", sign(assumptions[i])?"-":"", var(assumptions[i])+1);
//printf("\n");
    vec<Var> extra_frozen;
    lbool    result = l_True;

    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }

    if (result == l_True)
        result = Solver::solve_();
    else if (verbosity >= 1)
        printf("c ===============================================================================\n");

    if (result == l_True)
        extendModel();

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}


Lit SimpSolver::minElimVar(const Clause& c) const {
    Lit p = lit_Undef;
    for (int i = 0; i < c.size(); i++){
        int o = elim_order[var(c[i])];
        assert(o == 0 || value(c[i]) == l_Undef);
        if (o != 0 && (p == lit_Undef || o < elim_order[var(p)]))
            p = c[i];
    }
    return p;
}
bool SimpSolver::addOrSchedElim_(const vec<Lit>& ps)
{
//printf("c addOrSchedElim_:");
//for (int i = 0; i < ps.size(); i++) printf(" %s%d", sign(ps[i])?"-":"", var(ps[i])+1);
//printf("\n");
    if (ps.size() == 0)
        return false;
    else if (ps.size() == 1 && !isEliminated(var(ps[0])))
        return enqueue(ps[0]) && propagate() == CRef_Undef;

    CRef cr = ca.alloc(ps, false); // Allocate even if unit.
    ca[cr].mark(4); // Until actually added in 'addOrSchedElim__', assume detached.
    return addOrSchedElim__(cr);
}
bool SimpSolver::addOrSchedElim_(CRef cr)
{
    const Clause& c = ca[cr];

    if (c.size() == 0)
        return false;
    else if (c.size() == 1 && !isEliminated(var(c[0])))
        return enqueue(c[0]) && propagate() == CRef_Undef;

    return addOrSchedElim__(cr);
}
bool SimpSolver::addOrSchedElim__(CRef cr)
{
    Clause& c = ca[cr];
//printf("c addOrSchedElim__:");
//for (int i = 0; i < c.size(); i++) printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1);
//printf("\n");

    Lit p = minElimVar(c);
    if (p == lit_Undef){
        assert(c.size() > 1 && (c.mark() == 0 || c.mark() == 4));
        clauses.push(cr);
        attachClause(cr);
        c.mark(0);
    }else{
        assert(isEliminated(var(p)));
        if (c.size() == 1)
            elim_clauses[toInt(p)].clear();
#if 0
        else if (c.size() <= 2){ // Optional subsumption checking.
            vec<CRef>& elim = elim_clauses[toInt(p)];
            int i, j;
            for (i = j = 0; i < elim.size(); i++)
                if (c.subsumes(ca[elim[i]]) == lit_Undef)
                    elim[j++] = elim[i];
            elim.shrink(i - j); }
#endif
        to_resolve[toInt(p)].push(cr);

        if (!elim_heap_incr.inHeap(var(p)))
            elim_heap_incr.insert(var(p));
    }
    return true;
}


bool SimpSolver::addClauseIncr(vec<Lit>& ps)
{
    if (!ok) return false;
//printf("c addClauseIncr:");
//for (int i = 0; i < ps.size(); i++) printf(" %s%d", sign(ps[i])?"-":"", var(ps[i])+1);
//printf("\n");

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    return ok = addOrSchedElim_(ps);
}
bool SimpSolver::addOrSchedElimTrim(CRef cr)
{
    Clause& c = ca[cr]; // 'c' is either a new clause added incrementally or a revived clause from elimination.
    int i, j;
    for (i = j = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            c.mark(1);
            ca.free(cr);
            return true;
        }else if (value(c[i]) != l_False)
            c[j++] = c[i];
    c.shrink(i - j);
    ca.free_(i - j); // For correct memory usage calculation.

    return addOrSchedElim_(cr);
}

bool SimpSolver::goodToElim(Var v, const vec<CRef>& pos, const vec<CRef>& neg, int limit, int& cnt)
{
    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    int clause_size = 0;

    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > limit || (clause_lim != -1 && clause_size > clause_lim)))
                return false;

    return true;
}


bool SimpSolver::goodToElimIncr(Var v, const vec<CRef>&      pos, const vec<CRef>&      neg,
                                       const vec<CRef>& elim_pos, const vec<CRef>& elim_neg)
{
    assert(isEliminated(v));

    // The total number of clauses, from the perspective of the original problem,
    // should not increase before solving. However, this limit is an approximation.
    int limit = pos.size() + neg.size() + elim_pos.size() + elim_neg.size() + grow;

    int cnt = 0;
    return goodToElim(v,      pos,      neg, limit, cnt)
        && goodToElim(v,      pos, elim_neg, limit, cnt)
        && goodToElim(v, elim_pos,      neg, limit, cnt)
        && goodToElim(v, elim_pos, elim_neg, limit, cnt);
}


void SimpSolver::removeSatElimCls()
{
    for (int v = 0; v < nVars(); v++){
        Lit p = mkLit(v, false);
        if (value(p) != l_Undef)
            elim_clauses[value(p) == l_True ? toInt(p) : toInt(~p)].clear(); }
}
bool SimpSolver::resolveIncr(Var v, const vec<CRef>& pos, const vec<CRef>& neg)
{
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addOrSchedElim_(resolvent))
                return false;
    return true;
}
bool SimpSolver::eliminateIncr()
{
    removeSatElimCls();

    vec<char> assumed(nVars(), 0);
    for (int i = 0; i < assumptions.size(); i++){
        Var v = var(assumptions[i]);
        assumed[v] = 1;
        if (isEliminated(v) && !elim_heap_incr.inHeap(v))
            elim_heap_incr.insert(v); }

    while (ok && !elim_heap_incr.empty()){
        Var v = elim_heap_incr.removeMin();
        assert(isEliminated(v) && value(v) == l_Undef);

        Lit p = mkLit(v, false);
        vec<CRef>&      pos = to_resolve  [toInt( p)];
        vec<CRef>&      neg = to_resolve  [toInt(~p)];
        vec<CRef>& elim_pos = elim_clauses[toInt( p)];
        vec<CRef>& elim_neg = elim_clauses[toInt(~p)];
        assert(pos.size() != 0 || neg.size() != 0 || assumed[v]);
        //assert(elim_pos.size() != 0 || elim_neg.size() != 0);

        // TODO: Is it always good to not consume?
        if (false && !assumed[v] && goodToElimIncr(v, pos, neg, elim_pos, elim_neg)){
//printf("c Consuming %d.\n", v);
            if (!resolveIncr(v,      pos,      neg)
             || !resolveIncr(v,      pos, elim_neg)
             || !resolveIncr(v, elim_pos,      neg))
                return ok = false;
            append(pos, elim_pos);
            append(neg, elim_neg);
        }else{
//printf("c Reviving %d%s.\n", v, assumed[v]? " (assumed)":"");
            elim_order[v] = 0;
            setDecisionVar(v, true);
            eliminated_vars--;

            for (int i = 0; ok && i < elim_pos.size(); i++) ok = addOrSchedElimTrim(elim_pos[i]);
            for (int i = 0; ok && i < elim_neg.size(); i++) ok = addOrSchedElimTrim(elim_neg[i]);
            for (int i = 0; ok && i <      pos.size(); i++) ok = addOrSchedElimTrim(     pos[i]);
            for (int i = 0; ok && i <      neg.size(); i++) ok = addOrSchedElimTrim(     neg[i]);
            elim_pos.clear(), elim_neg.clear();
        }
        pos.clear(), neg.clear();
    }
    return ok;
}


bool SimpSolver::addClause_(vec<Lit>& ps)
{
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    int nclauses = clauses.size();

    if (use_rcheck && implied(ps))
        return true;

    if (!Solver::addClause_(ps))
        return false;

    if (use_simplification && clauses.size() == nclauses + 1){
        CRef          cr = clauses.last();
        const Clause& c  = ca[cr];

        // NOTE: the clause is added to the queue immediately and then
        // again during 'gatherTouchedClauses()'. If nothing happens
        // in between, it will only be checked once. Otherwise, it may
        // be checked twice unnecessarily. This is an unfortunate
        // consequence of how backward subsumption is used to mimic
        // forward subsumption.
        subsumption_queue.insert(cr);
        for (int i = 0; i < c.size(); i++){
            occurs[var(c[i])].push(cr);
            n_occ[toInt(c[i])]++;
            touched[var(c[i])] = 1;
            n_touched++;
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(CRef cr)
{
    const Clause& c = ca[cr];

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[toInt(c[i])]--;
            updateElimHeap(var(c[i]));
            occurs.smudge(var(c[i]));
        }

    Solver::removeClause(cr);
}


bool SimpSolver::strengthenClause(CRef cr, Lit l)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);
    assert(use_simplification);

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(cr);

    if (c.size() == 2){
        removeClause(cr);
        c.strengthen(l);
    }else{
        detachClause(cr, true);
        c.strengthen(l);
        attachClause(cr);
        remove(occurs[var(l)], cr);
        n_occ[toInt(l)]--;
        updateElimHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == CRef_Undef : true;
}


// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    // TODO: false literals while merging.
    // ~/sc13_application/satchal12-selected/Application_SAT+UNSAT/SATChallenge2012_Application/SAT_Competition_2011_unselected/SAT11/application/rintanen/SATPlanning/blocks-blocks-36-0.150-NOTKNOWN.cnf
    // ~/sc13_application/satchal12-selected/Application_SAT+UNSAT/SATChallenge2012_Application/SAT_Competition_2011_unselected/SAT11/application/rintanen/SATPlanning/blocks-blocks-36-0.130-NOTKNOWN.cnf

    // TODO: c.size() == 1 && value(c[0]) == l_Undef in 'strengthenClause'.
    // ~/sc13_application/satchal12-selected/Application_SAT+UNSAT/SATCompetition2007/industrial/babic/xinetd/itox_vc1130.cnf

    merges++;
    out_clause.clear();

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++) if (value(qs[i]) == l_True) return false;
    for (int i = 0; i < ps.size(); i++) if (value(ps[i]) == l_True) return false;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v && value(qs[i]) != l_False){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i]))
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v && value(ps[i]) != l_False)
            out_clause.push(ps[i]);

    return true;
}


// Returns FALSE if clause is always satisfied.
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size)
{
    merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;
    const Lit*  __ps  = (const Lit*)ps;
    const Lit*  __qs  = (const Lit*)qs;

    size = ps.size()-1;

    for (int i = 0; i < qs.size(); i++) if (value(__qs[i]) == l_True) return false;
    for (int i = 0; i < ps.size(); i++) if (value(__ps[i]) == l_True) return false;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v && value(__qs[i]) != l_False){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i]))
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
            size++;
        }
        next:;
    }

    return true;
}


void SimpSolver::gatherTouchedClauses()
{
    if (n_touched == 0) return;

    int i,j;
    for (i = j = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 0)
            ca[subsumption_queue[i]].mark(2);

    for (i = 0; i < nVars(); i++)
        if (touched[i]){
            const vec<CRef>& cs = occurs.lookup(i);
            for (j = 0; j < cs.size(); j++)
                if (ca[cs[j]].mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    ca[cs[j]].mark(2);
                }
            touched[i] = 0;
        }

    for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
            ca[subsumption_queue[i]].mark(0);

    n_touched = 0;
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return true;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != CRef_Undef;
    cancelUntil(0);
    return result;
}


// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
            subsumption_queue.clear();
            bwdsub_assigns = trail.size();
            break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            subsumption_queue.insert(bwdsub_tmpunit); }

        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            printf("c subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (c.mark())
                break;
            else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
                Lit l = c.subsumes(ca[cs[j]]);

                if (l == lit_Undef)
                    subsumed++, removeClause(cs[j]);
                else if (l != lit_Error){
                    deleted_literals++;

                    if (!strengthenClause(cs[j], ~l))
                        return false;

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
            }
    }

    return true;
}


bool SimpSolver::asymm(Var v, CRef cr)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v){
            if (value(c[i]) != l_False)
                uncheckedEnqueue(~c[i]);
        }else
            l = c[i];

    if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    assert(use_simplification);

    const vec<CRef>& cls = occurs.lookup(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
            return false;

    return backwardSubsumptionCheck();
}


#if 0
static void mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}
#endif


bool SimpSolver::eliminateVar(Var v)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    const vec<CRef>& cls = occurs.lookup(v);
    vec<CRef>        pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    int cnt = 0;
    if (!goodToElim(v, pos, neg, cls.size() + grow, cnt))
        return true;

    // Delete and store old clauses:
    elim_order[v] = elim_order_cnt++;
    setDecisionVar(v, false);
    eliminated_vars++;

    pos.copyTo(elim_clauses[toInt(mkLit(v, false))]);
    neg.copyTo(elim_clauses[toInt(mkLit(v, true ))]);
#if 0
    if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
            mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
    }else{
        for (int i = 0; i < pos.size(); i++)
            mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
    }
#endif

    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];
        for (int j = 0; j < c.size(); j++){
            n_occ[toInt(c[j])]--;
            updateElimHeap(var(c[j]));
            occurs.smudge(var(c[j]));
        }
        detachClause(cls[i]);
        c.mark(4); }

    // Produce clauses in cross product:
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
                return false;

    // Free occurs list for this variable:
    occurs[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    watches_bin[ mkLit(v)].clear(true);
    watches_bin[~mkLit(v)].clear(true);
    watches[ mkLit(v)].clear(true);
    watches[~mkLit(v)].clear(true);

    return backwardSubsumptionCheck();
}


bool SimpSolver::substitute(Var v, Lit x)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    if (!ok) return false;

    elim_order[v] = elim_order_cnt++;
    setDecisionVar(v, false);
    const vec<CRef>& cls = occurs.lookup(v);
    
    vec<Lit>& subst_clause = add_tmp;
    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];

        subst_clause.clear();
        for (int j = 0; j < c.size(); j++){
            Lit p = c[j];
            subst_clause.push(var(p) == v ? x ^ sign(p) : p);
        }

        removeClause(cls[i]);

        if (!addClause_(subst_clause))
            return ok = false;
    }

    return true;
}


void SimpSolver::extendModel()
{
    vec<Var> tmp;

    for (int x = 0; x < nVars(); x++){
        assert(modelValue(x) != l_Undef ||  isEliminated(x));
        assert(modelValue(x) == l_Undef || !isEliminated(x));
        if (isEliminated(x))
            tmp.push(x); }
    assert(tmp.size() == eliminated_vars);

    sort(tmp, ElimIncrLt(elim_order));
    for (int i = tmp.size()-1; i >= 0; i--){
        Lit p = mkLit(tmp[i], false);

        int j, k;
        const vec<CRef>& pos = elim_clauses[toInt(p)];
        for (j = 0; j < pos.size(); j++){
            const Clause& c = ca[pos[j]];
            for (k = 0; k < c.size() && modelValue(c[k]) != l_True; k++)
                assert(modelValue(c[k]) == l_False || c[k] == p);

            if (k == c.size())
                break; // This clause is not satisfied.
        }
        assert(modelValue(p) == l_Undef);
        model[var(p)] = lbool(j != pos.size()); // Does there exist a clause not yet satisfied?

        /* DEBUG for (int i = 0, j; i < pos.size(); i++){
            const Clause& c = ca[pos[i]];
            for (j = 0; j < c.size() && modelValue(c[j]) != l_True; j++)
                assert(modelValue(c[j]) != l_Undef);
            assert(j != c.size()); }
        const vec<CRef>& neg = elim_clauses[toInt(~p)];
        for (int i = 0, j; i < neg.size(); i++){
            const Clause& c = ca[neg[i]];
            for (j = 0; j < c.size() && modelValue(c[j]) != l_True; j++)
                assert(modelValue(c[j]) != l_Undef);
            assert(j != c.size()); }*/
    }
#if 0
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
            if (modelValue(toLit(elimclauses[i])) != l_False)
                goto next;

        x = toLit(elimclauses[i]);
        model[var(x)] = lbool(!sign(x));
    next:;
    }
#endif
}


bool SimpSolver::eliminate(bool turn_off_elim)
{
    if (!simplify())
        return false;
    else if (!use_simplification)
        return true;

    if (nVars() < 10000) goto cleanup; // Skip pre-processing for small problems.

    // Main simplification loop:
    //
    while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){

        gatherTouchedClauses();
        // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
        if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) && 
            !backwardSubsumptionCheck(true)){
            ok = false; goto cleanup; }

        // Empty elim_heap and return immediately on user-interrupt:
        if (asynch_interrupt){
            assert(bwdsub_assigns == trail.size());
            assert(subsumption_queue.size() == 0);
            assert(n_touched == 0);
            elim_heap.clear();
            goto cleanup; }

        // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            Var elim = elim_heap.removeMin();
            
            if (asynch_interrupt) break;

            if (isEliminated(elim) || value(elim) != l_Undef) continue;

            if (verbosity >= 2 && cnt % 100 == 0)
                printf("c elimination left: %10d\r", elim_heap.size());

            if (use_asymm){
                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                bool was_frozen = frozen[elim];
                frozen[elim] = true;
                if (!asymmVar(elim)){
                    ok = false; goto cleanup; }
                frozen[elim] = was_frozen; }

            // At this point, the variable may have been set by assymetric branching, so check it
            // again. Also, don't eliminate frozen variables:
            if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                ok = false; goto cleanup; }

            checkGarbage(simp_garbage_frac);
        }

        assert(subsumption_queue.size() == 0);
    }
 cleanup:

    // If no more simplification is needed, free all simplification-related data structures:
    if (turn_off_elim){
        touched  .clear(true);
        occurs   .clear(true);
        n_occ    .clear(true);
        elim_heap.clear(true);
        subsumption_queue.clear(true);

        use_simplification    = false;
        remove_satisfied      = true;
        ca.extra_clause_field = false;

        // Force full cleanup (this is safe and desirable since it only happens once):
        rebuildOrderHeap();
        garbageCollect();
    }else{
        checkGarbage();
    }

#if 0
    if (verbosity >= 1 && elimclauses.size() > 0)
        printf("c |  Eliminated clauses:     %10.2f Mb                                      |\n", 
               double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024));
#endif

    return ok;
}


//=================================================================================================
// Garbage Collection methods:


void SimpSolver::relocAll(ClauseAllocator& to)
{
    for (int i = 0, j, k; i < elim_clauses.size(); i++){
        vec<CRef>& cs = elim_clauses[i];
        for (j = k = 0; j < cs.size(); j++)
            if (ca[cs[j]].mark() == 4)
                ca.reloc(cs[k++] = cs[j], to);
        cs.shrink(j - k);
    }

    if (!use_simplification) return;

    // All occurs lists:
    //
    occurs.cleanAll();
    for (int i = 0; i < nVars(); i++){
        vec<CRef>& cs = occurs[i];
        for (int j = 0; j < cs.size(); j++)
            ca.reloc(cs[j], to);
    }

    // Subsumption queue:
    //
    for (int i = 0; i < subsumption_queue.size(); i++)
        ca.reloc(subsumption_queue[i], to);

    // Temporary clause:
    //
    ca.reloc(bwdsub_tmpunit, to);
}


void SimpSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.
    relocAll(to);
    Solver::relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
