%------------------------------------------------------------------------------
% File     : SYO670-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_1_4
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_1_4 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   77 (   2 unt;  51 nHn;  76 RR)
%            Number of literals    :  728 (   0 equ; 604 neg)
%            Maximal clause size   :   17 (   9 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  124 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_775,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_4))))))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ 'E'(f(B_4),f(suc(suc(suc(B_4)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_909,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_10))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_10))))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_984,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_88,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_787,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_7))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_7))))))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_90,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1142,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_8),f(suc(suc(suc(B_8))))) ) ).

cnf(clause_921,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_49,axiom,
    ( ~ 'LE'(f(suc(B_7)),s(s('0')))
    | 'E'(s('0'),f(suc(B_7)))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_352,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_876,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_4))))))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ 'E'(f(B_4),f(suc(suc(suc(B_4)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_862,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_8),f(suc(suc(suc(B_8))))) ) ).

cnf(clause_23,axiom,
    ( ~ 'LE'(f(suc(suc(B_10))),s('0'))
    | 'E'('0',f(suc(suc(B_10))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_276,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_360,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_8))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8)) ) ).

cnf(clause_1064,axiom,
    ( ~ 'LE'(f(B_7),s(s('0')))
    | 'E'(s('0'),f(B_7))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_643,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_577,axiom,
    ( ~ 'LE'(f(suc(B_3)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_3)))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_222,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_684,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_555,axiom,
    ( ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_511,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_8))))))
    | ~ 'E'(f(B_8),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_582,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_364,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_1,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_11))))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

cnf(clause_172,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_84,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_244,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_291,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(B_4),f(suc(suc(suc(B_4))))) ) ).

cnf(clause_597,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_4),f(suc(suc(suc(B_4))))) ) ).

cnf(clause_803,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_10)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_10)))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_32,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_4),f(suc(suc(suc(B_4))))) ) ).

cnf(clause_292,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_893,axiom,
    ( ~ 'LE'(f(B_3),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_3))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_1155,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_34,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_410,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_330,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_3)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_3)))))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_478,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_11))))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

cnf(clause_463,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_759,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_4))))))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ 'E'(f(B_4),f(suc(suc(suc(B_4)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_1034,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_11))))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_1098,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_11),f(suc(suc(suc(B_11))))) ) ).

cnf(clause_912,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_1161,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_492,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_8))))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_758,axiom,
    ( ~ 'LE'(f(suc(suc(B_7))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_7))))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_766,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_8),f(suc(suc(suc(B_8))))) ) ).

cnf(clause_1165,axiom,
    ( ~ 'LE'(f(suc(suc(B_3))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_3))))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_471,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1033,axiom,
    ( ~ 'LE'(f(suc(B_10)),s('0'))
    | 'E'('0',f(suc(B_10)))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_983,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_986,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_1056,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_1042,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_7)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_7)))))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_66,axiom,
    ( ~ 'LE'(f(B_10),s('0'))
    | 'E'('0',f(B_10))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_372,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_28,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_4),f(suc(suc(suc(B_4))))) ) ).

cnf(clause_384,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_578,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_599,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_447,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(suc(suc(B_11))))) ) ).

cnf(clause_556,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_481,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_3))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(B_3))))))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_575,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_1145,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(B_8),f(suc(suc(suc(B_8))))) ) ).

cnf(clause_783,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1022,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_560,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_959,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_11),f(suc(suc(suc(B_11))))) ) ).

cnf(clause_596,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_11))))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(suc(B_11)))))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_280,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_918,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_730,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_8))))))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(B_8),f(suc(suc(suc(B_8)))))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_72,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_11),f(suc(suc(suc(B_11))))) ) ).

cnf(clause_539,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_4))))))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ 'E'(f(B_4),f(suc(suc(suc(B_4)))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4)) ) ).

cnf(clause_957,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

%------------------------------------------------------------------------------
