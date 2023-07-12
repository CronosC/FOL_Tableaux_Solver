%------------------------------------------------------------------------------
% File     : SYO657-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_1_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_1_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.3.0
% Syntax   : Number of clauses     :   20 (   2 unt;  10 nHn;  19 RR)
%            Number of literals    :  102 (   0 equ;  75 neg)
%            Maximal clause size   :    9 (   5 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   27 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_10,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_45,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_2))))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_17,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_23,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_56,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_31,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_9,axiom,
    ( ~ 'LE'(f(B_2),s(s('0')))
    | 'E'(s('0'),f(B_2))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_34,axiom,
    ( ~ 'LE'(f(B_5),s('0'))
    | 'E'('0',f(B_5))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_41,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_15,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_6)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_26,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_43,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(B_6))))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_6))
    | ~ 'E'('0',f(B_6))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | ~ 'E'('0',f(suc(B_6))) ) ).

cnf(clause_40,axiom,
    ( ~ 'LE'(f(suc(B_5)),s('0'))
    | 'E'('0',f(suc(B_5)))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_51,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s('0'))
    | 'E'('0',f(suc(suc(B_5))))
    | 'LE'(f(B_5),'0') ) ).

cnf(clause_24,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_32,axiom,
    ( ~ 'LE'(f(suc(B_2)),s(s('0')))
    | 'E'(s('0'),f(suc(B_2)))
    | 'LE'(f(B_2),s('0')) ) ).

cnf(clause_52,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_3),f(suc(B_3))) ) ).

cnf(clause_5,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_38,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_33,axiom,
    ( ~ iLEQ(suc(A_1),suc(B_3))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(suc(B_3))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(B_3)))
    | ~ 'E'(s('0'),f(B_3))
    | ~ 'E'(f(B_3),f(suc(B_3)))
    | ~ 'E'(f(A_1),f(suc(A_1))) ) ).

%------------------------------------------------------------------------------
