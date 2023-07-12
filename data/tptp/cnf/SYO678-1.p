%------------------------------------------------------------------------------
% File     : SYO678-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_1_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_1_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   66 (   2 unt;  40 nHn;  65 RR)
%            Number of literals    :  490 (   0 equ; 389 neg)
%            Maximal clause size   :   13 (   7 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  101 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_113,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_317,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_105,axiom,
    ( ~ 'LE'(f(suc(B_13)),s(s('0')))
    | 'E'(s('0'),f(suc(B_13)))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_350,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_9)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_9)))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_219,axiom,
    ( ~ 'LE'(f(B_9),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_9))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_345,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_273,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_441,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_154,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_226,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_14,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_4)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B_4)))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_71,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_402,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_396,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_280,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_38,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_45,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_237,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_388,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_414,axiom,
    ( ~ 'LE'(f(suc(suc(B_4))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_4))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_263,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_253,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_252,axiom,
    ( ~ 'LE'(f(suc(B_9)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_9)))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_328,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_410,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_13)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_13)))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_281,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_103,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_3,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_369,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_338,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_37,axiom,
    ( ~ 'LE'(f(suc(B_4)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_4)))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_133,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_16)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_16)))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_161,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_146,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_419,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_18,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_46,axiom,
    ( ~ 'LE'(f(suc(suc(B_9))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_9))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_233,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_322,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_292,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_244,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14)) ) ).

cnf(clause_351,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_334,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_447,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_424,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_330,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_246,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_147,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_442,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_197,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_11,axiom,
    ( ~ 'LE'(f(suc(B_16)),s('0'))
    | 'E'('0',f(suc(B_16)))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_326,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_160,axiom,
    ( ~ 'LE'(f(B_4),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_4))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_415,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_66,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s('0'))
    | 'E'('0',f(suc(suc(B_16))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_42,axiom,
    ( ~ 'LE'(f(B_13),s(s('0')))
    | 'E'(s('0'),f(B_13))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_91,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_455,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_139,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10)))) ) ).

cnf(clause_143,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_173,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_137,axiom,
    ( ~ 'LE'(f(suc(suc(B_13))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_13))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_423,axiom,
    ( ~ 'LE'(f(B_16),s('0'))
    | 'E'('0',f(B_16))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_425,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_202,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_311,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

%------------------------------------------------------------------------------
