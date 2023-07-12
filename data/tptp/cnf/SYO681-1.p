%------------------------------------------------------------------------------
% File     : SYO681-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_2_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_2_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   54 (   2 unt;  32 nHn;  53 RR)
%            Number of literals    :  474 (   0 equ; 389 neg)
%            Maximal clause size   :   14 (   8 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  117 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_658,axiom,
    ( ~ 'LE'(f(B_23),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_23))
    | 'LE'(f(B_23),s(s(s('0')))) ) ).

cnf(clause_592,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(suc(suc(B_54))))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_556,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_227,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_24))))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_80,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(suc(B_55))))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_330,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_300,axiom,
    ( ~ 'LE'(f(B_41),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_41))
    | 'LE'(f(B_41),s(s('0'))) ) ).

cnf(clause_415,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_614,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_61),f(suc(B_61)))
    | 'E'(f(B_62),f(suc(B_62))) ) ).

cnf(clause_607,axiom,
    ( ~ 'LE'(f(suc(suc(B_41))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_41))))
    | 'LE'(f(B_41),s(s('0'))) ) ).

cnf(clause_479,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_62),f(suc(B_62))) ) ).

cnf(clause_723,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_42))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_209,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'(f(B_62),f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(suc(B_62))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_486,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_687,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_54),f(suc(B_54)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_528,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_42))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_359,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_497,axiom,
    ( ~ 'LE'(f(B_60),s('0'))
    | 'E'('0',f(B_60))
    | 'LE'(f(B_60),'0') ) ).

cnf(clause_463,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_42),f(suc(B_42)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_534,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_228,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(B_54),f(suc(B_54)))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_95,axiom,
    ( ~ 'LE'(f(suc(B_53)),s(s('0')))
    | 'E'(s('0'),f(suc(B_53)))
    | 'LE'(f(B_53),s('0')) ) ).

cnf(clause_352,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_42))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_125,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_61,axiom,
    ( ~ 'LE'(f(suc(suc(B_60))),s('0'))
    | 'E'('0',f(suc(suc(B_60))))
    | 'LE'(f(B_60),'0') ) ).

cnf(clause_713,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_560,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_103,axiom,
    ( ~ 'LE'(f(suc(suc(B_23))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_23))))
    | 'LE'(f(B_23),s(s(s('0')))) ) ).

cnf(clause_563,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_450,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'(f(B_62),f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(suc(B_62))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_501,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_283,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_137,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_24))))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_457,axiom,
    ( ~ 'LE'(f(suc(B_41)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_41)))
    | 'LE'(f(B_41),s(s('0'))) ) ).

cnf(clause_515,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(f(B_43),f(suc(B_43)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_43))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_42),f(suc(B_42))) ) ).

cnf(clause_663,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_572,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(B_62),f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(suc(B_62))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_61),f(suc(B_61))) ) ).

cnf(clause_131,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_24))))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1))) ) ).

cnf(clause_458,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_62),f(suc(B_62))) ) ).

cnf(clause_41,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(suc(suc(B_54))))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(suc(B_55))))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(B_54)) ) ).

cnf(clause_223,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_61),f(suc(B_61)))
    | 'E'(f(B_62),f(suc(B_62))) ) ).

cnf(clause_44,axiom,
    ( ~ 'LE'(f(B_53),s(s('0')))
    | 'E'(s('0'),f(B_53))
    | 'LE'(f(B_53),s('0')) ) ).

cnf(clause_550,axiom,
    ( ~ 'LE'(f(suc(B_23)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_23)))
    | 'LE'(f(B_23),s(s(s('0')))) ) ).

cnf(clause_325,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(B_42))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_42),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_291,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_24))))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(f(B_24),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_25),f(suc(B_25))) ) ).

cnf(clause_383,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_473,axiom,
    ( ~ iLEQ(suc(B_24),suc(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_25))
    | ~ 'E'(s(s(s('0'))),f(B_24))
    | ~ iLEQ(suc(A_1),suc(B_24))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_25),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_24)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_25))))
    | ~ 'E'(s(s(s('0'))),f(suc(B_25)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_24),f(suc(B_24))) ) ).

cnf(clause_594,axiom,
    ( ~ 'E'(s(s('0')),f(suc(B_42)))
    | ~ 'E'(s(s('0')),f(B_42))
    | ~ iLEQ(suc(B_42),suc(B_43))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(B_43)))
    | ~ iLEQ(suc(A_2),suc(B_42))
    | ~ 'E'(s(s('0')),f(B_43))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_42),f(suc(B_42)))
    | 'E'(f(B_43),f(suc(B_43))) ) ).

cnf(clause_363,axiom,
    ( ~ 'E'('0',f(suc(B_61)))
    | ~ iLEQ(suc(B_61),suc(B_62))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_61))
    | ~ 'E'('0',f(suc(B_62)))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(B_62),f(suc(B_62)))
    | ~ 'E'('0',f(B_61))
    | ~ 'E'('0',f(suc(suc(B_62))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(B_62))
    | ~ 'E'('0',f(suc(suc(B_61))))
    | ~ 'E'(f(B_61),f(suc(B_61)))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_145,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(suc(B_55))))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(B_54),f(suc(B_54))) ) ).

cnf(clause_595,axiom,
    ( ~ 'LE'(f(suc(B_60)),s('0'))
    | 'E'('0',f(suc(B_60)))
    | 'LE'(f(B_60),'0') ) ).

cnf(clause_508,axiom,
    ( ~ 'LE'(f(suc(suc(B_53))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_53))))
    | 'LE'(f(B_53),s('0')) ) ).

cnf(clause_671,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(suc(suc(B_54))))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(B_55),f(suc(B_55))) ) ).

cnf(clause_35,axiom,
    ( ~ iLEQ(suc(B_54),suc(B_55))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(B_55),f(suc(B_55)))
    | ~ iLEQ(suc(A_3),suc(B_54))
    | ~ 'E'(s('0'),f(suc(B_55)))
    | ~ 'E'(s('0'),f(suc(suc(B_54))))
    | ~ 'E'(f(B_54),f(suc(B_54)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(B_55))
    | ~ 'E'(s('0'),f(suc(suc(B_55))))
    | ~ 'E'(s('0'),f(suc(B_54)))
    | ~ 'E'(s('0'),f(B_54))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

%------------------------------------------------------------------------------
