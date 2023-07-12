%------------------------------------------------------------------------------
% File     : SYO685-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_1_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_1_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   47 (   2 unt;  25 nHn;  46 RR)
%            Number of literals    :  252 (   0 equ; 186 neg)
%            Maximal clause size   :    9 (   5 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   66 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_143,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_130,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_125,axiom,
    ( ~ 'LE'(f(B_16),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_16))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_61,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_169,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_208,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_28,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_97,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_16))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_74,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17)))) ) ).

cnf(clause_190,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_79,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_55,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_184,axiom,
    ( ~ 'LE'(f(B_20),s(s('0')))
    | 'E'(s('0'),f(B_20))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_94,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_191,axiom,
    ( ~ 'LE'(f(suc(B_5)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B_5)))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_93,axiom,
    ( ~ 'LE'(f(suc(suc(B_5))),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(suc(B_5))))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_40,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_95,axiom,
    ( ~ 'LE'(f(B_11),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_11))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_86,axiom,
    ( ~ 'LE'(f(suc(B_16)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_16)))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_96,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_175,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(suc(suc(B_21))))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(f(B_21),f(suc(B_21)))
    | ~ 'E'(s('0'),f(A_4)) ) ).

cnf(clause_49,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_52,axiom,
    ( ~ 'LE'(f(suc(suc(B_11))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_11))))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_154,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_36,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_194,axiom,
    ( ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_181,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_31,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_12),f(suc(B_12))) ) ).

cnf(clause_168,axiom,
    ( ~ 'LE'(f(suc(B_23)),s('0'))
    | 'E'('0',f(suc(B_23)))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_192,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(suc(A_4))))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_30,axiom,
    ( ~ 'LE'(f(suc(B_20)),s(s('0')))
    | 'E'(s('0'),f(suc(B_20)))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_87,axiom,
    ( ~ iLEQ(suc(A_4),suc(B_21))
    | ~ 'E'(s('0'),f(suc(B_21)))
    | ~ 'E'(s('0'),f(B_21))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_21),f(suc(B_21))) ) ).

cnf(clause_105,axiom,
    ( ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'('0',f(suc(suc(B_24))))
    | ~ iLEQ(suc(A_5),suc(B_24))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(B_24)))
    | ~ 'E'('0',f(B_24))
    | ~ 'E'(f(A_5),f(suc(A_5))) ) ).

cnf(clause_116,axiom,
    ( ~ 'LE'(f(suc(suc(B_20))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_20))))
    | 'LE'(f(B_20),s('0')) ) ).

cnf(clause_113,axiom,
    ( ~ 'LE'(f(B_5),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B_5))
    | 'LE'(f(B_5),s(s(s(s('0'))))) ) ).

cnf(clause_44,axiom,
    ( ~ 'E'('0',f(suc(suc(A_5))))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'(f(A_5),f(suc(A_5)))
    | ~ 'E'('0',f(A_5))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_34,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_111,axiom,
    ( ~ 'LE'(f(suc(B_11)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_11)))
    | 'LE'(f(B_11),s(s(s('0')))) ) ).

cnf(clause_19,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | 'E'(f(A_5),f(suc(A_5)))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_115,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_17))
    | ~ 'E'(s(s('0')),f(A_3))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_11,axiom,
    ( ~ 'LE'(f(suc(suc(B_23))),s('0'))
    | 'E'('0',f(suc(suc(B_23))))
    | 'LE'(f(B_23),'0') ) ).

cnf(clause_9,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_73,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_12))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_12))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(f(B_12),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_12)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_12))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_204,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_53,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_183,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_6))
    | ~ iLEQ(suc(A_1),suc(B_6))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(B_6))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_6)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(f(B_6),f(suc(B_6))) ) ).

cnf(clause_173,axiom,
    ( ~ 'LE'(f(B_23),s('0'))
    | 'E'('0',f(B_23))
    | 'LE'(f(B_23),'0') ) ).

%------------------------------------------------------------------------------
