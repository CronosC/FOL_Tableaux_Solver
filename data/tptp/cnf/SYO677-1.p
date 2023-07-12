%------------------------------------------------------------------------------
% File     : SYO677-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_1_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_1_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   38 (   2 unt;  20 nHn;  37 RR)
%            Number of literals    :  202 (   0 equ; 149 neg)
%            Maximal clause size   :    9 (   5 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   53 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_24,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10)))) ) ).

cnf(clause_23,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_143,axiom,
    ( ~ 'LE'(f(suc(suc(B_4))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_4))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_59,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_7,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_38,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_15,axiom,
    ( ~ 'LE'(f(B_13),s(s('0')))
    | 'E'(s('0'),f(B_13))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_74,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_13,axiom,
    ( ~ 'LE'(f(suc(B_4)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_4)))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_51,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_91,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_97,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2,axiom,
    ( ~ 'LE'(f(suc(B_16)),s('0'))
    | 'E'('0',f(suc(B_16)))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_145,axiom,
    ( ~ 'LE'(f(B_16),s('0'))
    | 'E'('0',f(B_16))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_18,axiom,
    ( ~ 'LE'(f(suc(suc(B_9))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_9))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_61,axiom,
    ( ~ 'LE'(f(B_4),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_4))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_0,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_113,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_73,axiom,
    ( ~ 'LE'(f(B_9),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_9))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_48,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_10,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_140,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_150,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_31,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_39,axiom,
    ( ~ 'LE'(f(suc(B_13)),s(s('0')))
    | 'E'(s('0'),f(suc(B_13)))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_11,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_49,axiom,
    ( ~ 'LE'(f(suc(suc(B_13))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_13))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_77,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_57,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14)) ) ).

cnf(clause_121,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1))) ) ).

cnf(clause_87,axiom,
    ( ~ 'LE'(f(suc(B_9)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_9)))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_65,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_99,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_84,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_112,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_27,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s('0'))
    | 'E'('0',f(suc(suc(B_16))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_115,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_114,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

%------------------------------------------------------------------------------
