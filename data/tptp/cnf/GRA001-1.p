%------------------------------------------------------------------------------
% File     : GRA001-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Graph Theory
% Problem  : Clauses from a labelled graph
% Version  : Especial.
% English  : Consider a graph with the edges labelled. For example
%                          *       :
%                      A /   \ B   :
%                       *--C--*    :
%                      D \   / E   :
%                          *       :
%            Assign 0 or 1 arbitarily to nodes of the graph. For each node
%            of the graph, we associate a set of clauses as follows :
%            (1) Every label of an edge emanating from that node will
%                occur in each clause (of the set of clauses generated
%                from that node).
%            (2) If the node is assigned 0, then the number of negated
%                literals in each of the generated clauses is to be odd.
%                Generate all such clauses for that node.
%            (3) If the node is assigned 1, then the number of negated
%                literals in each of the generated clauses is to be even.
%                Generate all such clauses for that node.
%            Tseitin's result is this: the sum (mod 2) of the 0's and 1's
%            assigned to the nodes of the graph equals 1 iff the set
%            of generated clauses is inconsistent. For example, if the top
%            node of the above graph is assigned 1, and all other nodes
%            0, then the set of generated clauses will be inconsistent.

% Refs     : [Tse83] Tseitin (1983), On the Complexity of Derivations in Pr
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 74 [Pel86]

% Status   : Unsatisfiable
% Rating   : 0.00 v4.1.0, 0.20 v3.7.0, 0.25 v3.5.0, 0.00 v3.3.0, 0.33 v3.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   12 (   0 unt;   7 nHn;  12 RR)
%            Number of literals    :   32 (   0 equ;  16 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    5 (   5 usr;   5 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : CNF_UNS_PRP

% Comments : There is a graph which can be used to produce a problem
%            equivalent to Pelletier 71. This is described in Pelletier 74.
%------------------------------------------------------------------------------
%----From the top node, which was assigned 1. Therefore there must
%----be an even number of negated literals.
cnf(clause_1,negated_conjecture,
    ( a
    | b ) ).

cnf(clause_2,negated_conjecture,
    ( ~ a
    | ~ b ) ).

%----From the left node, which was assigned 0. Therefore there must
%----be an odd number of negated literals.
cnf(clause_3,negated_conjecture,
    ( a
    | c
    | ~ d ) ).

cnf(clause_4,negated_conjecture,
    ( a
    | ~ c
    | d ) ).

cnf(clause_5,negated_conjecture,
    ( ~ a
    | c
    | d ) ).

cnf(clause_6,negated_conjecture,
    ( ~ a
    | ~ c
    | ~ d ) ).

%----From the right node, which was assigned 0. Therefore there must
%----be an odd number of negated literals.
cnf(clause_7,negated_conjecture,
    ( b
    | c
    | ~ e ) ).

cnf(clause_8,negated_conjecture,
    ( b
    | ~ c
    | e ) ).

cnf(clause_9,negated_conjecture,
    ( ~ b
    | c
    | e ) ).

cnf(clause_10,negated_conjecture,
    ( ~ b
    | ~ c
    | ~ e ) ).

%----From the bottom node, which was assigned 0. Therefore there must
%----be an odd number of negated literals.
cnf(clause_11,negated_conjecture,
    ( d
    | ~ e ) ).

cnf(clause_12,negated_conjecture,
    ( ~ d
    | e ) ).

%------------------------------------------------------------------------------
