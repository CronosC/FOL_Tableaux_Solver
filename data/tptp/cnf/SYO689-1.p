%------------------------------------------------------------------------------
% File     : SYO689-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_5_5_1
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_5_5_1 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   22 (   2 unt;  10 nHn;  21 RR)
%            Number of literals    :  132 (   0 equ; 106 neg)
%            Maximal clause size   :   17 (   6 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   46 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_1581,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1218,axiom,
    ( ~ 'E'(s(s('0')),f(A_3))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_327,axiom,
    ( ~ 'E'(s('0'),f(suc(B_1137)))
    | ~ 'E'(s('0'),f(B_1140))
    | ~ 'E'(s('0'),f(suc(B_1139)))
    | ~ iLEQ(suc(B_1138),suc(B_1139))
    | ~ 'E'(s('0'),f(B_1141))
    | ~ 'E'(s('0'),f(B_1137))
    | ~ 'E'(s('0'),f(suc(B_1138)))
    | ~ iLEQ(suc(B_1137),suc(B_1138))
    | ~ iLEQ(suc(A_4),suc(B_1137))
    | ~ iLEQ(suc(B_1139),suc(B_1140))
    | ~ 'E'(s('0'),f(suc(B_1140)))
    | ~ iLEQ(suc(B_1140),suc(B_1141))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | ~ 'E'(s('0'),f(suc(B_1141)))
    | ~ 'E'(s('0'),f(B_1139))
    | ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(B_1138)) ) ).

cnf(clause_583,axiom,
    'LE'(f(A),s(s(s(s(s('0')))))) ).

cnf(clause_740,axiom,
    ( ~ 'LE'(f(B_1136),s(s('0')))
    | 'E'(s('0'),f(B_1136))
    | 'LE'(f(B_1136),s('0')) ) ).

cnf(clause_388,axiom,
    ( ~ 'LE'(f(suc(B_1066)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_1066)))
    | 'LE'(f(B_1066),s(s('0'))) ) ).

cnf(clause_657,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_907))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | ~ 'E'(s(s(s('0'))),f(B_911))
    | ~ 'E'(s(s(s('0'))),f(B_910))
    | ~ iLEQ(suc(B_909),suc(B_910))
    | ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(B_910)))
    | ~ 'E'(s(s(s('0'))),f(B_908))
    | ~ iLEQ(suc(A_2),suc(B_907))
    | ~ iLEQ(suc(B_908),suc(B_909))
    | ~ 'E'(s(s(s('0'))),f(suc(B_908)))
    | ~ 'E'(s(s(s('0'))),f(B_909))
    | ~ 'E'(s(s(s('0'))),f(suc(B_911)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_907)))
    | ~ iLEQ(suc(B_910),suc(B_911))
    | ~ iLEQ(suc(B_907),suc(B_908))
    | ~ 'E'(s(s(s('0'))),f(suc(B_909))) ) ).

cnf(clause_328,axiom,
    ( ~ 'LE'(f(B_1161),s('0'))
    | 'E'('0',f(B_1161))
    | 'LE'(f(B_1161),'0') ) ).

cnf(clause_1314,axiom,
    ( ~ 'LE'(f(B_1066),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_1066))
    | 'LE'(f(B_1066),s(s('0'))) ) ).

cnf(clause_2293,axiom,
    ( ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(suc(A_5)))
    | iLEQ(suc(A_5),suc(A_5)) ) ).

cnf(clause_1092,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_1230,axiom,
    ( ~ 'LE'(f(B_906),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_906))
    | 'LE'(f(B_906),s(s(s('0')))) ) ).

cnf(clause_421,axiom,
    ( ~ 'E'('0',f(B_1165))
    | ~ iLEQ(suc(B_1162),suc(B_1163))
    | ~ 'E'('0',f(suc(B_1163)))
    | ~ iLEQ(suc(A_5),suc(B_1162))
    | ~ 'E'('0',f(A_5))
    | ~ 'E'('0',f(B_1162))
    | ~ 'E'('0',f(B_1164))
    | ~ 'E'('0',f(suc(A_5)))
    | ~ 'E'('0',f(suc(B_1166)))
    | ~ 'E'('0',f(B_1166))
    | ~ iLEQ(suc(B_1165),suc(B_1166))
    | ~ iLEQ(suc(B_1163),suc(B_1164))
    | ~ 'E'('0',f(suc(B_1165)))
    | ~ 'E'('0',f(suc(B_1164)))
    | ~ 'E'('0',f(suc(B_1162)))
    | ~ iLEQ(suc(B_1164),suc(B_1165))
    | ~ 'E'('0',f(B_1163)) ) ).

cnf(clause_1514,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(B_588))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_588)))
    | ~ iLEQ(suc(B_586),suc(B_587))
    | ~ iLEQ(suc(B_588),suc(B_589))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_587)))
    | ~ 'E'(s(s(s(s('0')))),f(B_589))
    | ~ 'E'(s(s(s(s('0')))),f(B_590))
    | ~ iLEQ(suc(B_587),suc(B_588))
    | ~ 'E'(s(s(s(s('0')))),f(B_586))
    | ~ iLEQ(suc(B_589),suc(B_590))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_590)))
    | ~ 'E'(s(s(s(s('0')))),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_586))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_586)))
    | ~ 'E'(s(s(s(s('0')))),f(A_1))
    | ~ 'E'(s(s(s(s('0')))),f(suc(B_589)))
    | ~ 'E'(s(s(s(s('0')))),f(B_587)) ) ).

cnf(clause_1329,axiom,
    ( ~ 'E'(s('0'),f(A_4))
    | ~ 'E'(s('0'),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1935,axiom,
    ( ~ 'LE'(f(suc(B_906)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_906)))
    | 'LE'(f(B_906),s(s(s('0')))) ) ).

cnf(clause_2115,axiom,
    ( ~ 'LE'(f(B_585),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(B_585))
    | 'LE'(f(B_585),s(s(s(s('0'))))) ) ).

cnf(clause_2227,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_2))
    | ~ 'E'(s(s(s('0'))),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1440,axiom,
    ( ~ 'LE'(f(suc(B_1136)),s(s('0')))
    | 'E'(s('0'),f(suc(B_1136)))
    | 'LE'(f(B_1136),s('0')) ) ).

cnf(clause_2050,axiom,
    ( ~ 'LE'(f(suc(B_585)),s(s(s(s(s('0'))))))
    | 'E'(s(s(s(s('0')))),f(suc(B_585)))
    | 'LE'(f(B_585),s(s(s(s('0'))))) ) ).

cnf(clause_1712,axiom,
    ( ~ 'E'(s(s('0')),f(B_1069))
    | ~ 'E'(s(s('0')),f(suc(B_1067)))
    | ~ 'E'(s(s('0')),f(B_1070))
    | ~ 'E'(s(s('0')),f(B_1068))
    | ~ 'E'(s(s('0')),f(suc(B_1068)))
    | ~ iLEQ(suc(B_1067),suc(B_1068))
    | ~ 'E'(s(s('0')),f(suc(A_3)))
    | ~ 'E'(s(s('0')),f(B_1067))
    | ~ iLEQ(suc(B_1068),suc(B_1069))
    | ~ 'E'(s(s('0')),f(B_1071))
    | ~ iLEQ(suc(A_3),suc(B_1067))
    | ~ 'E'(s(s('0')),f(suc(B_1069)))
    | ~ iLEQ(suc(B_1069),suc(B_1070))
    | ~ 'E'(s(s('0')),f(suc(B_1071)))
    | ~ 'E'(s(s('0')),f(suc(B_1070)))
    | ~ 'E'(s(s('0')),f(A_3))
    | ~ iLEQ(suc(B_1070),suc(B_1071)) ) ).

cnf(clause_113,axiom,
    ( ~ 'LE'(f(suc(B_1161)),s('0'))
    | 'E'('0',f(suc(B_1161)))
    | 'LE'(f(B_1161),'0') ) ).

%------------------------------------------------------------------------------
