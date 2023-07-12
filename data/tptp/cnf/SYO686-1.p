%------------------------------------------------------------------------------
% File     : SYO686-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_1_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_1_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   82 (   2 unt;  50 nHn;  81 RR)
%            Number of literals    :  612 (   0 equ; 486 neg)
%            Maximal clause size   :   13 (   7 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  126 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_91,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_465,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_322,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_380,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_59,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | 'E'(f(A_5),f(suc(A_5)))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_340,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_92,axiom,
    ( ~ 'LE'(f(suc(B_20)),s(s('0')))
    | 'E'(s('0'),f(suc(B_20)))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_15,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_313,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_20)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_20)))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_327,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_11)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B_11)))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_511,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_493,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_191,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_226,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17)))) ) ).

cnf(clause_575,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_159,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_432,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_614,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_600,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_638,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_308,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_489,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_569,axiom,
    ( ~ 'LE'(f(suc(B_5)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B_5)))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_494,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_354,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_328,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_86,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_478,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_23)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_23)))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_643,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_300,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_16))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_5,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_181,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_355,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_102,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_558,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_232,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_16)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_16)))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_414,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_310,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_139,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_431,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_263,axiom,
    ( ~ 'LE'(f(suc(B_16)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_16)))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_518,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_93,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_267,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_294,axiom,
    ( ~ 'LE'(f(B_11),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_11))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_456,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_579,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_57,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_342,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_250,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_425,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_282,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_5))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_615,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_235,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_41,axiom,
    ( ~ 'LE'(f(suc(suc(B_23))),s('0'))
    | 'E'('0',f(suc(suc(B_23))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_503,axiom,
    ( ~ 'LE'(f(B_23),s('0'))
    | 'E'('0',f(B_23))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_149,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_64,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_610,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_335,axiom,
    ( ~ 'LE'(f(suc(B_11)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_11)))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_297,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_642,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_444,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_323,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_368,axiom,
    ( ~ 'LE'(f(B_16),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_16))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_567,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_264,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_550,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_573,axiom,
    ( ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(A_5))
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_356,axiom,
    ( ~ 'LE'(f(suc(suc(B_20))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_20))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_603,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_5)))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_5)))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_105,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_374,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_384,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_601,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_158,axiom,
    ( ~ 'LE'(f(suc(suc(B_11))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_11))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_295,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_98,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_345,axiom,
    ( ~ 'LE'(f(B_5),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B_5))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_216,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_534,axiom,
    ( ~ 'LE'(f(B_20),s(s('0')))
    | 'E'(s('0'),f(B_20))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_486,axiom,
    ( ~ 'LE'(f(suc(B_23)),s('0'))
    | 'E'('0',f(suc(B_23)))
    | 'LE'(f(B_23),'0') ) ).

%------------------------------------------------------------------------------
