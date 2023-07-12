%------------------------------------------------------------------------------
% File     : SYO671-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_2_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_2_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   41 (   2 unt;  24 nHn;  40 RR)
%            Number of literals    :  356 (   0 equ; 292 neg)
%            Maximal clause size   :   14 (   8 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   88 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_66,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_123,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_206,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_183,axiom,
    ( ~ 'LE'(f(suc(B_16)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_16)))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_26,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_217,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_16))))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_350,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_20,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17)))) ) ).

cnf(clause_16,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_326,axiom,
    ( ~ 'LE'(f(B_28),s(s('0')))
    | 'E'(s('0'),f(B_28))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_421,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_219,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30)))) ) ).

cnf(clause_311,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_83,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37)) ) ).

cnf(clause_37,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_86,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_232,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_17))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_49,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_94,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_351,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(B_18))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(B_18),f(suc(B_18)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_60,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_61,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_72,axiom,
    ( ~ 'LE'(f(suc(suc(B_35))),s('0'))
    | 'E'('0',f(suc(suc(B_35))))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_91,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_144,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_146,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_261,axiom,
    ( ~ 'LE'(f(B_16),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_16))
    | 'LE'(f(B_16),s(s('0'))) ) ).

cnf(clause_116,axiom,
    ( ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_340,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_29),f(suc(B_29)))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_353,axiom,
    ( ~ 'LE'(f(suc(B_35)),s('0'))
    | 'E'('0',f(suc(B_35)))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_82,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_189,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36)))
    | 'E'(f(B_37),f(suc(B_37))) ) ).

cnf(clause_205,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_17)))
    | ~ 'E'(s(s('0')),f(B_17))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ iLEQ(suc(B_17),suc(B_18))
    | ~ 'E'(s(s('0')),f(B_18))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_17))
    | ~ 'E'(s(s('0')),f(suc(suc(A_1))))
    | ~ 'E'(s(s('0')),f(suc(B_18)))
    | 'E'(f(B_17),f(suc(B_17)))
    | 'E'(f(B_18),f(suc(B_18))) ) ).

cnf(clause_211,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_110,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(f(B_29),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(B_29))))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s('0'),f(A_2))
    | 'E'(f(B_30),f(suc(B_30))) ) ).

cnf(clause_138,axiom,
    ( ~ 'LE'(f(suc(B_28)),s(s('0')))
    | 'E'(s('0'),f(suc(B_28)))
    | 'LE'(f(B_28),s('0')) ) ).

cnf(clause_77,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(suc(A_3))))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(B_36),f(suc(B_36))) ) ).

cnf(clause_67,axiom,
    ( ~ 'E'(s('0'),f(B_30))
    | ~ 'E'(s('0'),f(suc(B_30)))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_29))
    | ~ 'E'(s('0'),f(B_29))
    | ~ iLEQ(suc(B_29),suc(B_30))
    | ~ 'E'(s('0'),f(suc(B_29)))
    | ~ 'E'(s('0'),f(suc(suc(A_2))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_30),f(suc(B_30)))
    | ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(suc(B_30))))
    | 'E'(f(B_29),f(suc(B_29))) ) ).

cnf(clause_266,axiom,
    ( ~ 'E'('0',f(B_36))
    | ~ 'E'('0',f(suc(suc(B_36))))
    | ~ 'E'('0',f(suc(suc(B_37))))
    | ~ 'E'('0',f(suc(B_36)))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'(f(B_36),f(suc(B_36)))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_37)))
    | ~ 'E'('0',f(B_37))
    | ~ 'E'(f(B_37),f(suc(B_37)))
    | ~ iLEQ(suc(A_3),suc(B_36))
    | ~ iLEQ(suc(B_36),suc(B_37))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_307,axiom,
    ( ~ 'LE'(f(B_35),s('0'))
    | 'E'('0',f(B_35))
    | 'LE'(f(B_35),'0') ) ).

cnf(clause_18,axiom,
    ( ~ 'LE'(f(suc(suc(B_28))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_28))))
    | 'LE'(f(B_28),s('0')) ) ).

%------------------------------------------------------------------------------
