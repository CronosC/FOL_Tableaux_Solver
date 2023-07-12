%------------------------------------------------------------------------------
% File     : SYO669-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_1_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_1_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   50 (   2 unt;  30 nHn;  49 RR)
%            Number of literals    :  368 (   0 equ; 292 neg)
%            Maximal clause size   :   13 (   7 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   76 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_59,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_257,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_88,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_3)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_3)))))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_246,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_262,axiom,
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
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_301,axiom,
    ( ~ 'LE'(f(suc(suc(B_3))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_3))))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_207,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_10)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_10)))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_179,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_18,axiom,
    ( ~ 'LE'(f(B_10),s('0'))
    | 'E'('0',f(B_10))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_12,axiom,
    ( ~ 'LE'(f(suc(B_7)),s(s('0')))
    | 'E'(s('0'),f(suc(B_7)))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_106,axiom,
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

cnf(clause_267,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_139,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_299,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_25,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_9,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(suc(B_11)))))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'(f(B_11),f(suc(suc(B_11))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_260,axiom,
    ( ~ 'LE'(f(suc(B_10)),s('0'))
    | 'E'('0',f(suc(B_10)))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_295,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(suc(suc(A_3)))))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_121,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_144,axiom,
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

cnf(clause_292,axiom,
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
    | ~ iLEQ(suc(A_2),suc(B_8)) ) ).

cnf(clause_27,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_7,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_4,axiom,
    ( ~ 'LE'(f(suc(suc(B_10))),s('0'))
    | 'E'('0',f(suc(suc(B_10))))
    | 'LE'(f(B_10),'0') ) ).

cnf(clause_100,axiom,
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
    | ~ 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_276,axiom,
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
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_55,axiom,
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
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_44,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_87,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(B_4),f(suc(suc(B_4))))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_4)))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_248,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_11),f(suc(B_11))) ) ).

cnf(clause_153,axiom,
    ( ~ 'LE'(f(suc(B_3)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_3)))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_122,axiom,
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
    | ~ 'E'(s(s('0')),f(B_4)) ) ).

cnf(clause_272,axiom,
    ( ~ 'LE'(f(B_7),s(s('0')))
    | 'E'(s('0'),f(B_7))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_76,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_95,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(B_4),f(suc(B_4))) ) ).

cnf(clause_196,axiom,
    ( ~ 'LE'(f(suc(suc(B_7))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_7))))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_143,axiom,
    ( ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_247,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_8),f(suc(suc(B_8)))) ) ).

cnf(clause_72,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_222,axiom,
    ( ~ 'LE'(f(B_3),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_3))
    | 'LE'(f(B_3),s(s('0'))) ) ).

cnf(clause_167,axiom,
    ( ~ 'E'('0',f(suc(B_11)))
    | ~ 'E'('0',f(suc(suc(B_11))))
    | ~ 'E'('0',f(B_11))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_11))
    | ~ 'E'(f(B_11),f(suc(B_11)))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_11),f(suc(suc(B_11)))) ) ).

cnf(clause_90,axiom,
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
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_229,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(f(B_4),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_4))
    | ~ 'E'(s(s('0')),f(suc(suc(B_4))))
    | ~ 'E'(s(s('0')),f(suc(B_4)))
    | ~ 'E'(s(s('0')),f(B_4))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_4),f(suc(suc(B_4)))) ) ).

cnf(clause_74,axiom,
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

cnf(clause_151,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_181,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(suc(B_8))))
    | ~ 'E'(f(B_8),f(suc(suc(B_8))))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(f(B_8),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_8)))))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_236,axiom,
    ( ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(B_8))
    | ~ 'E'(s('0'),f(suc(B_8)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(A_2),suc(B_8))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_8),f(suc(B_8))) ) ).

cnf(clause_263,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_7)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_7)))))
    | 'LE'(f(B_7),s('0')) ) ).

cnf(clause_278,axiom,
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
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_33,axiom,
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
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

%------------------------------------------------------------------------------
