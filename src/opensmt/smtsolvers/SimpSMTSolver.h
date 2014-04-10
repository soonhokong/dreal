/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

/************************************************************************************[SimpSMTSolver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

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

#ifndef SIMP_SMT_SOLVER_H
#define SIMP_SMT_SOLVER_H

#include "minisat/mtl/Queue.h"
#include "CoreSMTSolver.h"

class SimpSMTSolver : public CoreSMTSolver
{
 public:
    // Constructor/Destructor:
    //
    SimpSMTSolver ( Egraph &, SMTConfig & );
    ~SimpSMTSolver( );

    bool         addSMTClause         ( vector< Enode * > &, uint64_t in = 0 );
    inline Minisat::lbool smtSolve             ( ) { return solve( false, false ); }
    inline Minisat::lbool smtSolve             ( bool do_simp ) { return solve( do_simp, false ); }
    Enode *      mergeTAtoms          ( Enode *, bool, Enode *, bool, Enode * );
    void         eliminateTVar        ( Enode * );
    void         initialize           ( );

#if NEW_SIMPLIFICATIONS
    void         gatherTVars          ( Enode *, bool, Minisat::Clause * );
    void         gaussianElimination  ( );
    void         substituteInClauses  ( );
    bool         dpfm                 ( );
#else
    void         getDLVars            ( Enode *, bool, Enode **, Enode ** );
#endif

    void         gatherInterfaceTerms ( Enode * );

    set< Minisat::Clause * >                      to_remove;
    vector< Minisat::Clause * >                   unary_to_remove;
#if NEW_SIMPLIFICATIONS
    set< Enode * >                       t_var; // Theory variables
#else
    // TODO: change to vector< list< Clauses * > >
    map< Enode *, set< enodeid_t > >     t_var; // Variables to which is connected to
#endif
    map< enodeid_t, vector< Minisat::Clause * > > t_pos; // Clauses where theory variable appears positively
    map< enodeid_t, vector< Minisat::Clause * > > t_neg; // Clauses where theory variable appears negatively

#if NEW_SIMPLIFICATIONS
    vector< LAExpression * >             var_to_lae;
#endif

    // Problem specification:
    //
    Minisat::Var     newVar    (bool polarity = true, bool dvar = true);
    bool    addClause (Minisat::vec<Minisat::Lit>& ps, uint64_t in = 0);

    // Variable mode:
    //
    void    setFrozen (Minisat::Var v, bool b); // If a variable is frozen it will not be eliminated.

    // Solving:
    //
    Minisat::lbool   solve     ( const Minisat::vec< Enode * > &, bool = true   , bool = false );
    Minisat::lbool   solve     ( const Minisat::vec< Enode * > &, const unsigned, bool = true, bool = false );
    Minisat::lbool   solve     ( const Minisat::vec< Minisat::Lit > &    , bool = true   , bool = false );
    Minisat::lbool   solve     ( const Minisat::vec< Minisat::Lit > &    , const unsigned, bool = true, bool = false );
    Minisat::lbool   solve     ( bool = true, bool = false );
    bool    eliminate ( bool = false);             // Perform variable elimination based simplification.

    // Generate a (possibly simplified) DIMACS file:
    //
    void    toDimacs  (const char* file);

    // Mode of operation:
    //
    int     grow;             // Allow a variable elimination step to grow by a number of clauses (default to zero).
    bool    asymm_mode;       // Shrink clauses by asymmetric branching.
    bool    redundancy_check; // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)

    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int     remembered_clauses;

// protected:
  public:

    // Helper structures:
    //
    struct ElimData {
        int          order;      // 0 means not eliminated, >0 gives an index in the elimination order
        Minisat::vec<Minisat::Clause*> eliminated;
        ElimData() : order(0) {} };

    struct ElimOrderLt {
        const Minisat::vec<ElimData>& elimtable;
        ElimOrderLt(const Minisat::vec<ElimData>& et) : elimtable(et) {}
        bool operator()(Minisat::Var x, Minisat::Var y) { return elimtable[x].order > elimtable[y].order; } };

    struct ElimLt {
        const Minisat::vec<int>& n_occ;
        ElimLt(const Minisat::vec<int>& no) : n_occ(no) {}
        int  cost      (Minisat::Var x)        const { return n_occ[Minisat::toInt(Minisat::mkLit(x))] * n_occ[Minisat::toInt(~Minisat::mkLit(x))]; }
        bool operator()(Minisat::Var x, Minisat::Var y) const { return cost(x) < cost(y); } };


    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    Minisat::vec<ElimData>       elimtable;
    Minisat::vec<char>           touched;
    Minisat::vec<Minisat::vec<Minisat::Clause*> >  occurs;
    Minisat::vec<int>            n_occ;
    Minisat::Heap<int, ElimLt>        elim_heap;
    Minisat::Queue<Minisat::Clause*>      subsumption_queue;
    Minisat::vec<char>           frozen;
    int                 bwdsub_assigns;

    // Temporaries:
    //
    Minisat::Clause*             bwdsub_tmpunit;

    // Main internal methods:
    //
    bool          asymm                    (Minisat::Var v, Minisat::Clause& c);
    bool          asymmVar                 (Minisat::Var v);
    void          updateElimHeap           (Minisat::Var v);
    void          cleanOcc                 (Minisat::Var v);
    Minisat::vec<Minisat::Clause*>& getOccurs                (Minisat::Var x);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Minisat::Clause& _ps, const Minisat::Clause& _qs, Minisat::Var v, Minisat::vec<Minisat::Lit>& out_clause);
    bool          merge                    (const Minisat::Clause& _ps, const Minisat::Clause& _qs, Minisat::Var v);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Minisat::Var v, bool fail = false);
    void          remember                 (Minisat::Var v);
    void          extendModel              ();
    void          verifyModel              ();

    void          removeClause             (Minisat::Clause& c);
    bool          strengthenClause         (Minisat::Clause& c, Minisat::Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const Minisat::vec<Minisat::Lit>& c);
    void          toDimacs                 (FILE* f, Minisat::Clause& c);
    bool          isEliminated             (Minisat::Var v) const;
};


//=================================================================================================
// Implementation of inline methods:

inline void SimpSMTSolver::updateElimHeap(Minisat::Var v) {
    if (elimtable[v].order == 0)
        elim_heap.update(v); }

inline void SimpSMTSolver::cleanOcc(Minisat::Var v)
{
    assert(use_simplification);
    Minisat::Clause **begin = (Minisat::Clause**)occurs[v];
    Minisat::Clause **end = begin + occurs[v].size();
    Minisat::Clause **i, **j;
    for (i = begin, j = end; i < j; i++)
        if ((*i)->mark() == 1){
            *i = *(--j);
            i--;
        }
    //occurs[v].shrink_(end - j);  // This seems slower. Why?!
    occurs[v].shrink(end - j);
}

inline Minisat::vec<Minisat::Clause*>& SimpSMTSolver::getOccurs(Minisat::Var x) {
    cleanOcc(x); return occurs[x]; }

inline bool  SimpSMTSolver::isEliminated (Minisat::Var v) const { return v < elimtable.size() && elimtable[v].order != 0; }
inline void  SimpSMTSolver::setFrozen    (Minisat::Var v, bool b) { if ( !use_simplification ) return; frozen[v] = (char)b; if (b) { updateElimHeap(v); } }
inline Minisat::lbool SimpSMTSolver::solve        (bool do_simp, bool turn_off_simp) { Minisat::vec<Minisat::Lit> tmp; return solve(tmp, do_simp, turn_off_simp); }

//=================================================================================================

#endif
