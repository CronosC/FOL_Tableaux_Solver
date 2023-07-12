%------------------------------------------------------------------------------
% File     : SYO674-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_3_5_1
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_3_5_1 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :   14 (   2 unt;   6 nHn;  13 RR)
%            Number of literals    :   80 (   0 equ;  64 neg)
%            Maximal clause size   :   17 (   5 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   28 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_193,axiom,
    ( ~ 'E'(s('0'),f(suc(B_233)))
    | ~ 'E'(s('0'),f(suc(B_232)))
    | ~ iLEQ(suc(B_230),suc(B_231))
    | ~ 'E'(s('0'),f(B_229))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | ~ 'E'(s('0'),f(suc(B_229)))
    | ~ 'E'(s('0'),f(B_232))
    | ~ 'E'(s('0'),f(B_233))
    | ~ 'E'(s('0'),f(B_231))
    | ~ iLEQ(suc(A_2),suc(B_229))
    | ~ iLEQ(suc(B_229),suc(B_230))
    | ~ 'E'(s('0'),f(suc(B_231)))
    | ~ 'E'(s('0'),f(B_230))
    | ~ 'E'(s('0'),f(suc(B_230)))
    | ~ iLEQ(suc(B_232),suc(B_233))
    | ~ 'E'(s('0'),f(A_2))
    | ~ iLEQ(suc(B_231),suc(B_232)) ) ).

cnf(clause_298,axiom,
    ( ~ 'LE'(f(B_228),s(s('0')))
    | 'E'(s('0'),f(B_228))
    | 'LE'(f(B_228),s('0')) ) ).

cnf(clause_281,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_176,axiom,
    ( ~ 'LE'(f(B_253),s('0'))
    | 'E'('0',f(B_253))
    | 'LE'(f(B_253),'0') ) ).

cnf(clause_139,axiom,
    ( ~ 'LE'(f(B_158),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_158))
    | 'LE'(f(B_158),s(s('0'))) ) ).

cnf(clause_126,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_498,axiom,
    'LE'(f(A),s(s(s('0')))) ).

cnf(clause_204,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_129,axiom,
    ( ~ 'LE'(f(suc(B_158)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_158)))
    | 'LE'(f(B_158),s(s('0'))) ) ).

cnf(clause_431,axiom,
    ( ~ 'E'(s(s('0')),f(A_1))
    | ~ 'E'(s(s('0')),f(suc(B_163)))
    | ~ 'E'(s(s('0')),f(B_159))
    | ~ iLEQ(suc(B_160),suc(B_161))
    | ~ 'E'(s(s('0')),f(suc(A_1)))
    | ~ 'E'(s(s('0')),f(B_162))
    | ~ 'E'(s(s('0')),f(B_163))
    | ~ iLEQ(suc(B_159),suc(B_160))
    | ~ 'E'(s(s('0')),f(suc(B_161)))
    | ~ 'E'(s(s('0')),f(suc(B_160)))
    | ~ 'E'(s(s('0')),f(suc(B_162)))
    | ~ 'E'(s(s('0')),f(B_160))
    | ~ iLEQ(suc(B_161),suc(B_162))
    | ~ 'E'(s(s('0')),f(B_161))
    | ~ 'E'(s(s('0')),f(suc(B_159)))
    | ~ iLEQ(suc(B_162),suc(B_163))
    | ~ iLEQ(suc(A_1),suc(B_159)) ) ).

cnf(clause_50,axiom,
    ( ~ 'LE'(f(suc(B_253)),s('0'))
    | 'E'('0',f(suc(B_253)))
    | 'LE'(f(B_253),'0') ) ).

cnf(clause_84,axiom,
    ( ~ 'LE'(f(suc(B_228)),s(s('0')))
    | 'E'(s('0'),f(suc(B_228)))
    | 'LE'(f(B_228),s('0')) ) ).

cnf(clause_493,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_453,axiom,
    ( ~ iLEQ(suc(A_3),suc(B_254))
    | ~ 'E'('0',f(B_254))
    | ~ 'E'('0',f(suc(B_257)))
    | ~ iLEQ(suc(B_255),suc(B_256))
    | ~ 'E'('0',f(B_258))
    | ~ iLEQ(suc(B_256),suc(B_257))
    | ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(B_255))
    | ~ 'E'('0',f(suc(B_254)))
    | ~ iLEQ(suc(B_254),suc(B_255))
    | ~ 'E'('0',f(suc(A_3)))
    | ~ 'E'('0',f(suc(B_256)))
    | ~ iLEQ(suc(B_257),suc(B_258))
    | ~ 'E'('0',f(suc(B_255)))
    | ~ 'E'('0',f(suc(B_258)))
    | ~ 'E'('0',f(B_256))
    | ~ 'E'('0',f(B_257)) ) ).

%------------------------------------------------------------------------------
