%------------------------------------------------------------------------------
% File     : SYO682-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_3_2
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_3_2 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   86 (   2 unt;  60 nHn;  85 RR)
%            Number of literals    : 1162 (   0 equ; 997 neg)
%            Maximal clause size   :   19 (  13 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  277 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_2815,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_1739,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69))) ) ).

cnf(clause_1492,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_2548,axiom,
    ( ~ 'LE'(f(suc(suc(B_149))),s('0'))
    | 'E'('0',f(suc(suc(B_149))))
    | 'LE'(f(B_149),'0') ) ).

cnf(clause_1268,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_151),f(suc(B_151)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_911,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_139),f(suc(B_139))) ) ).

cnf(clause_1275,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3)))) ) ).

cnf(clause_2710,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1331,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_114),f(suc(B_114))) ) ).

cnf(clause_2217,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1737,axiom,
    ( ~ 'LE'(f(suc(suc(B_68))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_68))))
    | 'LE'(f(B_68),s(s(s('0')))) ) ).

cnf(clause_2645,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_2463,axiom,
    ( ~ 'LE'(f(suc(B_137)),s(s('0')))
    | 'E'(s('0'),f(suc(B_137)))
    | 'LE'(f(B_137),s('0')) ) ).

cnf(clause_2971,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_139),f(suc(B_139)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_1807,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_114),f(suc(B_114))) ) ).

cnf(clause_550,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_2031,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_826,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_138),f(suc(B_138))) ) ).

cnf(clause_1838,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_114),f(suc(B_114)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_1045,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_2487,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1914,axiom,
    ( ~ 'LE'(f(B_137),s(s('0')))
    | 'E'(s('0'),f(B_137))
    | 'LE'(f(B_137),s('0')) ) ).

cnf(clause_2205,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_147,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_151),f(suc(B_151))) ) ).

cnf(clause_1622,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_1979,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_1537,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1799,axiom,
    ( ~ 'LE'(f(suc(suc(B_137))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_137))))
    | 'LE'(f(B_137),s('0')) ) ).

cnf(clause_2033,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_70),f(suc(B_70)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_2038,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_114),f(suc(B_114)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_1815,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_150),f(suc(B_150))) ) ).

cnf(clause_1226,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_151),f(suc(B_151))) ) ).

cnf(clause_1197,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_2895,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_596,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_139),f(suc(B_139)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_2388,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_2537,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_138),f(suc(B_138))) ) ).

cnf(clause_1178,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_1497,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_139),f(suc(B_139))) ) ).

cnf(clause_491,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_1684,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1006,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_139),f(suc(B_139))) ) ).

cnf(clause_165,axiom,
    ( ~ 'LE'(f(B_149),s('0'))
    | 'E'('0',f(B_149))
    | 'LE'(f(B_149),'0') ) ).

cnf(clause_190,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1))) ) ).

cnf(clause_2237,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_70),f(suc(B_70))) ) ).

cnf(clause_2902,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_17,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_114),f(suc(B_114)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_777,axiom,
    ( ~ 'LE'(f(B_68),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_68))
    | 'LE'(f(B_68),s(s(s('0')))) ) ).

cnf(clause_2749,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151))) ) ).

cnf(clause_2717,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113))) ) ).

cnf(clause_2619,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_2240,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_1450,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_1577,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(B_71))))
    | ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(f(B_71),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_797,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(B_139),f(suc(B_139)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_258,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_1145,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(s('0'),f(suc(suc(B_140))))
    | ~ 'E'(f(B_140),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_139),f(suc(B_139))) ) ).

cnf(clause_2543,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_2433,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_151),f(suc(B_151))) ) ).

cnf(clause_2414,axiom,
    ( ~ 'LE'(f(B_112),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_112))
    | 'LE'(f(B_112),s(s('0'))) ) ).

cnf(clause_625,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_151),f(suc(B_151)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_2576,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_151),f(suc(B_151)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_409,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_2497,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(f(B_70),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_70))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_885,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(B_150))))
    | ~ 'E'(f(B_150),f(suc(B_150)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_2752,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_114),f(suc(B_114))) ) ).

cnf(clause_2897,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_679,axiom,
    ( ~ 'LE'(f(suc(suc(B_112))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_112))))
    | 'LE'(f(B_112),s(s('0'))) ) ).

cnf(clause_705,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(B_113),f(suc(B_113))) ) ).

cnf(clause_1426,axiom,
    ( ~ 'LE'(f(suc(B_68)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_68)))
    | 'LE'(f(B_68),s(s(s('0')))) ) ).

cnf(clause_2044,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_2923,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_69),f(suc(B_69)))
    | 'E'(f(B_70),f(suc(B_70)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_2095,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_113),f(suc(B_113)))
    | 'E'(f(B_114),f(suc(B_114)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_2084,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(f(B_138),f(suc(B_138)))
    | ~ 'E'(f(B_139),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(suc(B_139))))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(B_138))))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_2899,axiom,
    ( ~ 'E'(s('0'),f(suc(B_140)))
    | ~ 'E'(s('0'),f(B_140))
    | ~ 'E'(s('0'),f(suc(B_138)))
    | ~ 'E'(s('0'),f(B_138))
    | ~ 'E'(s('0'),f(suc(B_139)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ iLEQ(suc(B_139),suc(B_140))
    | ~ 'E'(s('0'),f(B_139))
    | ~ iLEQ(suc(A_3),suc(B_138))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(B_138),suc(B_139))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_138),f(suc(B_138)))
    | 'E'(f(B_139),f(suc(B_139)))
    | 'E'(f(B_140),f(suc(B_140))) ) ).

cnf(clause_2704,axiom,
    ( ~ 'LE'(f(suc(B_149)),s('0'))
    | 'E'('0',f(suc(B_149)))
    | 'LE'(f(B_149),'0') ) ).

cnf(clause_134,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_115))))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_115),f(suc(B_115)))
    | 'E'(f(B_114),f(suc(B_114))) ) ).

cnf(clause_1230,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_151),f(suc(B_151))) ) ).

cnf(clause_1659,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_2160,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_151),f(suc(B_151)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_591,axiom,
    ( ~ iLEQ(suc(A_2),suc(B_113))
    | ~ 'E'(f(B_113),f(suc(B_113)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_114))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(B_114),suc(B_115))
    | ~ 'E'(s(s('0')),f(suc(suc(B_113))))
    | ~ 'E'(s(s('0')),f(B_115))
    | ~ 'E'(s(s('0')),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(B_114))
    | ~ 'E'(s(s('0')),f(B_113))
    | ~ iLEQ(suc(B_113),suc(B_114))
    | ~ 'E'(s(s('0')),f(suc(B_115)))
    | ~ 'E'(f(B_114),f(suc(B_114)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(B_113)))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_115),f(suc(B_115))) ) ).

cnf(clause_1409,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(suc(suc(B_152))))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'(f(B_152),f(suc(B_152)))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(B_150),f(suc(B_150))) ) ).

cnf(clause_988,axiom,
    ( ~ 'LE'(f(suc(B_112)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_112)))
    | 'LE'(f(B_112),s(s('0'))) ) ).

cnf(clause_1709,axiom,
    ( ~ 'E'(s(s(s('0'))),f(B_69))
    | ~ 'E'(s(s(s('0'))),f(suc(B_70)))
    | ~ 'E'(s(s(s('0'))),f(suc(B_71)))
    | ~ 'E'(s(s(s('0'))),f(B_70))
    | ~ 'E'(s(s(s('0'))),f(suc(B_69)))
    | ~ iLEQ(suc(B_70),suc(B_71))
    | ~ 'E'(f(B_69),f(suc(B_69)))
    | ~ iLEQ(suc(B_69),suc(B_70))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_69))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ iLEQ(suc(A_1),suc(B_69))
    | ~ 'E'(s(s(s('0'))),f(B_71))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(B_70),f(suc(B_70)))
    | 'E'(f(B_71),f(suc(B_71))) ) ).

cnf(clause_2861,axiom,
    ( ~ 'E'('0',f(B_152))
    | ~ 'E'('0',f(B_151))
    | ~ iLEQ(suc(B_151),suc(B_152))
    | ~ 'E'('0',f(suc(B_150)))
    | ~ 'E'('0',f(B_150))
    | ~ 'E'('0',f(suc(suc(B_151))))
    | ~ 'E'('0',f(suc(B_152)))
    | ~ iLEQ(suc(B_150),suc(B_151))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_151),f(suc(B_151)))
    | ~ iLEQ(suc(A_4),suc(B_150))
    | ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(B_151)))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_150),f(suc(B_150)))
    | 'E'(f(B_152),f(suc(B_152))) ) ).

cnf(clause_1131,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

%------------------------------------------------------------------------------
