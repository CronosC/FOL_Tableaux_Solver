%--------------------------------------------------------------------------
% File     : SWV011-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Software Verification
% Problem  : Fact 2 of the Neumann-Stubblebine analysis
% Version  : [Wei99] axioms.
% English  :

% Refs     : [Wei99] Weidenbach (1999), Towards and Automatic Analysis of S
%            [Bau99] Baumgartner (1999), FTP'2000 - Problem Sets
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   3 RR)
%            Number of literals    :    4 (   0 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :    1 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created by tptp2X -f tptp -t cnf:otter SWV011+1.p
%--------------------------------------------------------------------------
cnf(ax1_11,axiom,
    b_holds(key(generate_key(an_a_nonce),a)) ).

cnf(ax3_13,axiom,
    a_holds(key(generate_key(an_a_nonce),b)) ).

cnf(co1_17,negated_conjecture,
    ( ~ a_holds(key(A,b))
    | ~ b_holds(key(A,a)) ) ).

%--------------------------------------------------------------------------
