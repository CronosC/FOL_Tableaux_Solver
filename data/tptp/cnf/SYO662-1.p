%------------------------------------------------------------------------------
% File     : SYO662-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_2_2_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_2_2_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   70 (   2 unt;  52 nHn;  69 RR)
%            Number of literals    :  924 (   0 equ; 789 neg)
%            Maximal clause size   :   20 (  13 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  177 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_651,axiom,
    ( ~ 'LE'(f(B_10),s(s('0')))
    | 'E'(s('0'),f(B_10))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_887,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_1118,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_629,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_592,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_1113,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_102,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_10,axiom,
    ( ~ 'LE'(f(B_17),s('0'))
    | 'E'('0',f(B_17))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_326,axiom,
    ( ~ 'LE'(f(suc(B_17)),s('0'))
    | 'E'('0',f(suc(B_17)))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_190,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_1095,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_968,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_502,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_1116,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_722,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12)) ) ).

cnf(clause_494,axiom,
    ( ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_915,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_110,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_846,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_854,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_864,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_754,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_105,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_98,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_598,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_605,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_214,axiom,
    ( ~ 'LE'(f(suc(suc(B_10))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_10))))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_27,axiom,
    ( ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'('0',f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_234,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_923,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_635,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_736,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_848,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_1146,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_1145,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_17)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_17)))))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_613,axiom,
    ( ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_918,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_871,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_944,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_597,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_242,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_452,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_10)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_10)))))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_983,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_130,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_703,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_748,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_168,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_956,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_543,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_806,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_1036,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_18),f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(suc(suc(B_18)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_19),f(suc(B_19))) ) ).

cnf(clause_1159,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_274,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_505,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_335,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_1002,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_138,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_58,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_655,axiom,
    ( ~ 'LE'(f(suc(B_10)),s(s('0')))
    | 'E'(s('0'),f(suc(B_10)))
    | 'LE'(f(B_10),s('0')) ) ).

cnf(clause_410,axiom,
    'LE'(f(A),s(s('0'))) ).

cnf(clause_998,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(f(B_19),f(suc(suc(B_19))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(suc(suc(suc(B_19)))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18)))) ) ).

cnf(clause_137,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(suc(B_11))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_420,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_287,axiom,
    ( ~ 'LE'(f(suc(suc(B_17))),s('0'))
    | 'E'('0',f(suc(suc(B_17))))
    | 'LE'(f(B_17),'0') ) ).

cnf(clause_1051,axiom,
    ( ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(B_18)))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

cnf(clause_128,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_520,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_226,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(suc(suc(A_1))))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s('0'),f(B_11))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_960,axiom,
    ( ~ 'E'(s('0'),f(suc(B_11)))
    | ~ 'E'(s('0'),f(B_12))
    | ~ 'E'(s('0'),f(A_1))
    | ~ 'E'(s('0'),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(A_1)))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_11)))))
    | ~ 'E'(s('0'),f(suc(suc(B_11))))
    | ~ 'E'(s('0'),f(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ iLEQ(suc(A_1),suc(B_11))
    | ~ iLEQ(suc(B_11),suc(B_12))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_1006,axiom,
    ( ~ 'E'('0',f(suc(suc(B_18))))
    | ~ 'E'('0',f(suc(A_2)))
    | ~ 'E'('0',f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'('0',f(suc(B_19)))
    | ~ iLEQ(suc(B_18),suc(B_19))
    | ~ 'E'('0',f(A_2))
    | ~ 'E'('0',f(B_19))
    | ~ 'E'('0',f(suc(suc(B_19))))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'('0',f(B_18))
    | ~ 'E'('0',f(suc(B_18)))
    | ~ 'E'(f(B_19),f(suc(B_19)))
    | ~ 'E'('0',f(suc(suc(suc(A_2)))))
    | ~ iLEQ(suc(A_2),suc(B_18))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_18),f(suc(suc(B_18))))
    | 'E'(f(B_19),f(suc(suc(B_19)))) ) ).

%------------------------------------------------------------------------------
