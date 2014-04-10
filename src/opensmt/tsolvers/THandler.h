/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#ifndef THANDLER_H
#define THANDLER_H

#include "SMTConfig.h"
#include "Egraph.h"
#include "TSolver.h"

class SMTSolver; // Forward declaration

class THandler
{
public:

  THandler ( Egraph &      e
           , SMTConfig &   c
           , SMTSolver &   s
           , Minisat::vec< Minisat::Lit > &  t
           , Minisat::vec< int > &  l
           , Minisat::vec< char > & a
           , const Minisat::Var vt
           , const Minisat::Var vf )
    : core_solver        ( e )
    , config             ( c )
    , solver             ( s )
    , trail              ( t )
    , level              ( l )
    , assigns            ( a )
    , var_True           ( vt )
    , var_False          ( vf )
    , checked_trail_size ( 0 )
    , tatoms             ( 0 )
    , batoms             ( 0 )
    , tatoms_given       ( 0 )
  {
    // Reserve room for true and false
    var_to_enode   .resize( 65536, NULL );
    enode_id_to_var.resize( 65536, Minisat::var_Undef );
  }

  virtual ~THandler ( ) { }

  void    getConflict          ( Minisat::vec< Minisat::Lit > &, int & ); // Returns theory conflict in terms of literals
#ifdef PRODUCE_PROOF
  Enode * getInterpolants      ( );                     // Fill a vector with interpolants
#endif
  Minisat::Lit     getDeduction         ( );			// Returns a literal that is implied by the current state
  Minisat::Lit     getSuggestion        ( );			// Returns a literal that is suggested by the current state
  void    getReason            ( Minisat::Lit, Minisat::vec< Minisat::Lit > & );   // Returns the explanation for a deduced literal

  Minisat::Var     enodeToVar           ( Enode * );             // Converts enode into boolean variable. Create a new variable if needed
  Minisat::Lit     enodeToLit           ( Enode * );             // Converts enode into boolean literal. Create a new variable if needed
  Minisat::Lit     enodeToLit           ( Enode *, Minisat::Var & );      // Converts enode into boolean literal. Create a new variable if needed
  Enode * varToEnode           ( Minisat::Var );                 // Return the enode corresponding to a variable
  void    clearVar             ( Minisat::Var );                 // Clear a Var in translation table (used in incremental solving)

  bool    assertLits           ( );                     // Give to the TSolvers the newly added literals on the trail
  bool    check                ( bool );                // Check trail in the theories
  void    backtrack            ( );                     // Remove literals that are not anymore on the trail

  double  getAtomsRatio        ( ) { return (double)batoms/((double)tatoms + 1.0); }

  void    inform               ( );

  Minisat::lbool   evaluate             ( Enode * e ) { return core_solver.evaluate( e ); }

private:

  // Returns a random float 0 <= x < 1. Seed must never be 0.
  static inline double drand(double& seed)
  {
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
  }

  // Returns a random integer 0 <= x < size. Seed must never be 0.
  static inline int irand(double& seed, int size)
  {
    return (int)(drand(seed) * size);
  }

  void verifyCallWithExternalTool        ( bool, size_t );
  void verifyExplanationWithExternalTool ( vector< Enode * > & );
  void verifyDeductionWithExternalTool   ( Enode * = NULL );
  bool callCertifyingSolver              ( const char * );
#ifdef PRODUCE_PROOF
  void verifyInterpolantWithExternalTool ( vector< Enode * > &, Enode * );
#endif

#ifdef PEDANTIC_DEBUG
  bool  isOnTrail     ( Minisat::Lit );
#endif

  vector< Minisat::Var >       enode_id_to_var;          // Conversion EnodeID --> Var
  vector< Enode * >   var_to_enode;             // Conversion Var --> EnodeID

  Egraph &            core_solver;              // Pointer to Egraph that works as core solver
  SMTConfig &         config;                   // Reference to configuration
  SMTSolver &         solver;                   // Reference to SMT Solver
  Minisat::vec< Minisat::Lit > &        trail;                    // Reference to SMT Solver trail
  Minisat::vec< int > &        level;                    // Reference to SMT Solver level
  Minisat::vec< char > &       assigns;                  // Reference to SMT Solver assigns
  const Minisat::Var           var_True;                 // To specify constantly true atoms
  const Minisat::Var           var_False;                // To specify constantly false atoms
  vector< Enode * >   stack;                    // Stacked atoms
  size_t              checked_trail_size;       // Store last size of the trail checked by the solvers

  int                 tatoms;                   // Tracks theory atoms
  int                 batoms;                   // Tracks boolean atoms

  vector< bool >      tatoms_seen;              // Atoms seen
  unsigned            tatoms_given;             // Next atom to give
  vector< Enode * >   tatoms_list;              // List of tatoms to communicate later
  vector< bool >      tatoms_give;              // We might want not to give some atoms
};

#endif
