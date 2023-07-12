%------------------------------------------------------------------------------
% File     : SYO687-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_1_4
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_1_4 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.29 v8.1.0, 0.14 v7.5.0, 0.17 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :  127 (   2 unt;  85 nHn; 126 RR)
%            Number of literals    : 1212 (   0 equ;1006 neg)
%            Maximal clause size   :   17 (   9 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  206 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_1841,axiom,
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
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_1240,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(suc(suc(B_24))))) ) ).

cnf(clause_682,axiom,
    ( ~ 'LE'(f(suc(suc(B_11))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_11))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_1174,axiom,
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
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_2135,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_2107,axiom,
    ( ~ 'LE'(f(B_20),s(s('0')))
    | 'E'(s('0'),f(B_20))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_2273,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(B_12),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_12))))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1896,axiom,
    ( ~ 'LE'(f(suc(B_23)),s('0'))
    | 'E'('0',f(suc(B_23)))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_1473,axiom,
    ( ~ 'LE'(f(B_16),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_16))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_1019,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_24))))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'(f(B_24),f(suc(suc(suc(B_24)))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_1659,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_2054,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_161,axiom,
    ( ~ 'LE'(f(suc(suc(B_23))),s('0'))
    | 'E'('0',f(suc(suc(B_23))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_887,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_21))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(f(B_21),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(suc(suc(A_4))))) ) ).

cnf(clause_2053,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_5))))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B_5))))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_213,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_311,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_683,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_1912,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_374,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4))))))
    | 'E'(f(B_21),f(suc(suc(suc(B_21))))) ) ).

cnf(clause_455,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_24))))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'(f(B_24),f(suc(suc(suc(B_24)))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(A_5),f(suc(suc(suc(A_5))))) ) ).

cnf(clause_1522,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2472,axiom,
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
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_21),f(suc(suc(suc(B_21))))) ) ).

cnf(clause_1924,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4))))))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_1503,axiom,
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
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_1424,axiom,
    ( ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_2348,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1701,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_1405,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_1682,axiom,
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

cnf(clause_231,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | 'E'(f(A_5),f(suc(A_5)))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_380,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2066,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_1143,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_5))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_1769,axiom,
    ( ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_2443,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_1710,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1556,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_16))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(B_16))))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_1310,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4))))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1796,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_3,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(B_12),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_12))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_1598,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(B_12),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_12))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1539,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_381,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_540,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_19,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_355,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(suc(B_12))))) ) ).

cnf(clause_2321,axiom,
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
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_2369,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_5)))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_5)))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_1172,axiom,
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
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(suc(suc(B_24))))) ) ).

cnf(clause_2417,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_2226,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_475,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_26,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_2498,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_20))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_20))))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_1073,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_565,axiom,
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
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | 'E'(f(B_24),f(suc(suc(suc(B_24))))) ) ).

cnf(clause_953,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_16)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_16)))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_1605,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1196,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_818,axiom,
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
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_12),f(suc(suc(suc(B_12))))) ) ).

cnf(clause_2189,axiom,
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

cnf(clause_1697,axiom,
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

cnf(clause_1900,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_478,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_368,axiom,
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
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_603,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4))))))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_1188,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_2009,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_2405,axiom,
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
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_21),f(suc(suc(suc(B_21))))) ) ).

cnf(clause_881,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ 'E'(f(B_24),f(suc(B_24)))
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
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(suc(suc(B_24))))) ) ).

cnf(clause_409,axiom,
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
    | 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_1232,axiom,
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

cnf(clause_351,axiom,
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
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_1081,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_920,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17)))) ) ).

cnf(clause_1403,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_2337,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(B_12),f(suc(suc(suc(B_12)))))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_12))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_327,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(B_24),f(suc(suc(B_24)))) ) ).

cnf(clause_222,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1670,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_2293,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_24))))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'(f(B_24),f(suc(suc(suc(B_24)))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_1953,axiom,
    ( ~ 'LE'(f(B_23),s('0'))
    | 'E'('0',f(B_23))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_1635,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_17)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

cnf(clause_1897,axiom,
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
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_12),f(suc(suc(suc(B_12))))) ) ).

cnf(clause_80,axiom,
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
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_2500,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_415,axiom,
    ( ~ 'LE'(f(suc(B_20)),s(s('0')))
    | 'E'(s('0'),f(suc(B_20)))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_2214,axiom,
    ( ~ 'LE'(f(suc(B_5)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B_5)))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_1860,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_23)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_23)))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_2224,axiom,
    ( ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(A_5))
    | 'E'(f(A_5),f(suc(suc(A_5))))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_1060,axiom,
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
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_2159,axiom,
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

cnf(clause_232,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_1408,axiom,
    ( ~ 'LE'(f(suc(suc(B_20))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_20))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_1,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_1778,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(suc(B_6))))) ) ).

cnf(clause_971,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1752,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_1376,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_6),f(suc(suc(suc(B_6)))))
    | ~ 'E'(f(B_6),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(B_6)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(B_6))))))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_188,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_21))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(f(B_21),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_1366,axiom,
    ( ~ 'LE'(f(B_5),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B_5))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_216,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_21))))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(f(B_21),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_4)))))) ) ).

cnf(clause_734,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_23))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_23))))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_1524,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(B_6),f(suc(suc(B_6)))) ) ).

cnf(clause_1340,axiom,
    ( ~ 'LE'(f(suc(B_11)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_11)))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_1185,axiom,
    ( ~ 'LE'(f(B_11),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_11))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_1301,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_11)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B_11)))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_1248,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_20)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_20)))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_774,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_1204,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_16))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_1433,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(B_12)))) ) ).

cnf(clause_253,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ 'E'('0',f(suc(suc(suc(suc(B_24))))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(suc(suc(B_24)))))
    | ~ 'E'(f(B_24),f(suc(suc(B_24))))
    | ~ 'E'(f(B_24),f(suc(suc(suc(B_24)))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(A_5),f(suc(suc(A_5)))) ) ).

cnf(clause_1067,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_11))))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_11))))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_1502,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_2387,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(suc(B_21)))) ) ).

cnf(clause_2489,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_2289,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(A_5))))))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_472,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_1981,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1589,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_21))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(f(B_21),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_629,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_21)))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(f(B_21),f(suc(suc(B_21))))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(suc(suc(B_21))))) ) ).

cnf(clause_522,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_12)))))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(suc(B_12))))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(suc(suc(B_12))))) ) ).

cnf(clause_623,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_1064,axiom,
    ( ~ 'LE'(f(suc(B_16)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_16)))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_739,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_1034,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(suc(suc(A_5)))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(suc(A_5))))
    | 'E'(f(A_5),f(suc(suc(suc(A_5)))))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

%------------------------------------------------------------------------------
