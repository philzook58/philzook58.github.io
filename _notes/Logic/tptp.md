---
layout: post
title: TPTP dump
---


- [Axioms](#axioms)
  - [Agents](#agents)
    - [./AGT001+0.ax](#agt0010ax)
    - [./AGT001+1.ax](#agt0011ax)
    - [./AGT001+2.ax](#agt0012ax)
  - [Abstract Algebra](#abstract-algebra)
    - [./ALG001-0.ax](#alg001-0ax)
    - [./ALG002+0.ax](#alg0020ax)
    - [./ALG002-0.ax](#alg002-0ax)
    - [./ALG003^0.ax](#alg0030ax)
  - [Analysis](#analysis)
    - [./ANA001-0.ax](#ana001-0ax)
    - [./ANA002-0.ax](#ana002-0ax)
    - [./ANA003-0.ax](#ana003-0ax)
    - [./BIO001+0.ax](#bio0010ax)
    - [./BOO001-0.ax](#boo001-0ax)
    - [./BOO002-0.ax](#boo002-0ax)
    - [./BOO003-0.ax](#boo003-0ax)
    - [./BOO004-0.ax](#boo004-0ax)
  - [Category Theory](#category-theory)
    - [./CAT001-0.ax](#cat001-0ax)
    - [./CAT002-0.ax](#cat002-0ax)
    - [./CAT003-0.ax](#cat003-0ax)
    - [./CAT004-0.ax](#cat004-0ax)
  - [Combinatory Logic](#combinatory-logic)
    - [./COL001-0.ax](#col001-0ax)
    - [./COL002-0.ax](#col002-0ax)
    - [./COL002-1.ax](#col002-1ax)
  - [Computing Theory](#computing-theory)
    - [./COM001+0.ax](#com0010ax)
    - [./COM001+1.ax](#com0011ax)
  - [Commonsense Reasoning](#commonsense-reasoning)
    - [./CSR001+0.ax](#csr0010ax)
    - [./CSR001+1.ax](#csr0011ax)
    - [./CSR001+2.ax](#csr0012ax)
    - [./CSR001+3.ax](#csr0013ax)
    - [./CSR002+0.ax](#csr0020ax)
    - [./CSR002+1.ax](#csr0021ax)
    - [./CSR002+2.ax](#csr0022ax)
    - [./CSR002+3.ax](#csr0023ax)
    - [./CSR002+4.ax](#csr0024ax)
    - [./CSR002+5.ax](#csr0025ax)
    - [./CSR003+0.ax](#csr0030ax)
    - [./CSR003+1.ax](#csr0031ax)
    - [./CSR003+2.ax](#csr0032ax)
    - [./CSR003+3.ax](#csr0033ax)
    - [./CSR003+4.ax](#csr0034ax)
    - [./CSR003+5.ax](#csr0035ax)
    - [./CSR004+0.ax](#csr0040ax)
    - [./CSR005^0.ax](#csr0050ax)
    - [./CSR006+0.ax](#csr0060ax)
  - [Data Structures](#data-structures)
    - [./DAT001\_0.ax](#dat001_0ax)
    - [./DAT002=1.ax](#dat0021ax)
    - [./DAT002\_0.ax](#dat002_0ax)
    - [./DAT003\_0.ax](#dat003_0ax)
    - [./DAT004\_0.ax](#dat004_0ax)
    - [./DAT005\_0.ax](#dat005_0ax)
    - [./DAT006\_0.ax](#dat006_0ax)
  - [Field Theory](#field-theory)
    - [./FLD001-0.ax](#fld001-0ax)
    - [./FLD002-0.ax](#fld002-0ax)
  - [Geometry](#geometry)
    - [./GEO001-0.ax](#geo001-0ax)
    - [./GEO001-1.ax](#geo001-1ax)
    - [./GEO002-0.ax](#geo002-0ax)
    - [./GEO002-1.ax](#geo002-1ax)
    - [./GEO002-2.ax](#geo002-2ax)
    - [./GEO002-3.ax](#geo002-3ax)
    - [./GEO003-0.ax](#geo003-0ax)
    - [./GEO004+0.ax](#geo0040ax)
    - [./GEO004+1.ax](#geo0041ax)
    - [./GEO004+2.ax](#geo0042ax)
    - [./GEO004+3.ax](#geo0043ax)
    - [./GEO004-0.ax](#geo004-0ax)
    - [./GEO004-1.ax](#geo004-1ax)
    - [./GEO004-2.ax](#geo004-2ax)
    - [./GEO004-3.ax](#geo004-3ax)
    - [./GEO005-0.ax](#geo005-0ax)
    - [./GEO006+0.ax](#geo0060ax)
    - [./GEO006+1.ax](#geo0061ax)
    - [./GEO006+2.ax](#geo0062ax)
    - [./GEO006+3.ax](#geo0063ax)
    - [./GEO006+4.ax](#geo0064ax)
    - [./GEO006+5.ax](#geo0065ax)
    - [./GEO006+6.ax](#geo0066ax)
    - [./GEO007+0.ax](#geo0070ax)
    - [./GEO007+1.ax](#geo0071ax)
    - [./GEO008+0.ax](#geo0080ax)
    - [./GEO009+0.ax](#geo0090ax)
    - [./GEO010+0.ax](#geo0100ax)
    - [./GEO010+1.ax](#geo0101ax)
    - [./GEO011+0.ax](#geo0110ax)
    - [./GEO012+0.ax](#geo0120ax)
  - [Graph Theory](#graph-theory)
    - [./GRA001+0.ax](#gra0010ax)
  - [Group Theory](#group-theory)
    - [./GRP001-0.ax](#grp001-0ax)
    - [./GRP002-0.ax](#grp002-0ax)
    - [./GRP003+0.ax](#grp0030ax)
    - [./GRP003-0.ax](#grp003-0ax)
    - [./GRP003-1.ax](#grp003-1ax)
    - [./GRP003-2.ax](#grp003-2ax)
    - [./GRP004+0.ax](#grp0040ax)
    - [./GRP004-0.ax](#grp004-0ax)
    - [./GRP004-1.ax](#grp004-1ax)
    - [./GRP004-2.ax](#grp004-2ax)
    - [./GRP005-0.ax](#grp005-0ax)
    - [./GRP006-0.ax](#grp006-0ax)
    - [./GRP007+0.ax](#grp0070ax)
    - [./GRP008-0.ax](#grp008-0ax)
    - [./GRP008-1.ax](#grp008-1ax)
  - [Homological Algebra](#homological-algebra)
    - [./HAL001+0.ax](#hal0010ax)
  - [Henkin Models](#henkin-models)
    - [./HEN001-0.ax](#hen001-0ax)
    - [./HEN002-0.ax](#hen002-0ax)
    - [./HEN003-0.ax](#hen003-0ax)
  - [Hardware Creation](#hardware-creation)
    - [./HWC001-0.ax](#hwc001-0ax)
    - [./HWC002-0.ax](#hwc002-0ax)
  - [Hardware Verification](#hardware-verification)
    - [./HWV001-0.ax](#hwv001-0ax)
    - [./HWV001-1.ax](#hwv001-1ax)
    - [./HWV001-2.ax](#hwv001-2ax)
    - [./HWV002-0.ax](#hwv002-0ax)
    - [./HWV002-1.ax](#hwv002-1ax)
    - [./HWV002-2.ax](#hwv002-2ax)
    - [./HWV003-0.ax](#hwv003-0ax)
    - [./HWV004-0.ax](#hwv004-0ax)
  - [Kleene Algebra](#kleene-algebra)
    - [./KLE001+0.ax](#kle0010ax)
    - [./KLE001+1.ax](#kle0011ax)
    - [./KLE001+2.ax](#kle0012ax)
    - [./KLE001+3.ax](#kle0013ax)
    - [./KLE001+4.ax](#kle0014ax)
    - [./KLE001+5.ax](#kle0015ax)
    - [./KLE001+6.ax](#kle0016ax)
    - [./KLE001+7.ax](#kle0017ax)
    - [./KLE002+0.ax](#kle0020ax)
    - [./KLE003+0.ax](#kle0030ax)
    - [./KLE004+0.ax](#kle0040ax)
  - [Knowledge Representation](#knowledge-representation)
    - [./KRS001+0.ax](#krs0010ax)
    - [./KRS001+1.ax](#krs0011ax)
  - [Lattice Theory](#lattice-theory)
    - [./LAT001-0.ax](#lat001-0ax)
    - [./LAT001-1.ax](#lat001-1ax)
    - [./LAT001-2.ax](#lat001-2ax)
    - [./LAT001-3.ax](#lat001-3ax)
    - [./LAT001-4.ax](#lat001-4ax)
    - [./LAT002-0.ax](#lat002-0ax)
    - [./LAT003-0.ax](#lat003-0ax)
    - [./LAT004-0.ax](#lat004-0ax)
    - [./LAT005-0.ax](#lat005-0ax)
    - [./LAT006-0.ax](#lat006-0ax)
    - [./LAT006-1.ax](#lat006-1ax)
    - [./LAT006-2.ax](#lat006-2ax)
  - [Logic Calculi](#logic-calculi)
    - [./LCL001-0.ax](#lcl001-0ax)
    - [./LCL001-1.ax](#lcl001-1ax)
    - [./LCL001-2.ax](#lcl001-2ax)
    - [./LCL002-0.ax](#lcl002-0ax)
    - [./LCL002-1.ax](#lcl002-1ax)
    - [./LCL003-0.ax](#lcl003-0ax)
    - [./LCL004-0.ax](#lcl004-0ax)
    - [./LCL004-1.ax](#lcl004-1ax)
    - [./LCL004-2.ax](#lcl004-2ax)
    - [./LCL005-0.ax](#lcl005-0ax)
    - [./LCL006+0.ax](#lcl0060ax)
    - [./LCL006+1.ax](#lcl0061ax)
    - [./LCL006+2.ax](#lcl0062ax)
    - [./LCL006+3.ax](#lcl0063ax)
    - [./LCL006+4.ax](#lcl0064ax)
    - [./LCL006+5.ax](#lcl0065ax)
    - [./LCL007+0.ax](#lcl0070ax)
    - [./LCL007+1.ax](#lcl0071ax)
    - [./LCL007+2.ax](#lcl0072ax)
    - [./LCL007+3.ax](#lcl0073ax)
    - [./LCL007+4.ax](#lcl0074ax)
    - [./LCL007+5.ax](#lcl0075ax)
    - [./LCL007+6.ax](#lcl0076ax)
    - [./LCL008^0.ax](#lcl0080ax)
    - [./LCL009^0.ax](#lcl0090ax)
    - [./LCL010^0.ax](#lcl0100ax)
    - [./LCL011^0.ax](#lcl0110ax)
    - [./LCL012^0.ax](#lcl0120ax)
    - [./LCL013^0.ax](#lcl0130ax)
    - [./LCL013^1.ax](#lcl0131ax)
    - [./LCL013^2.ax](#lcl0132ax)
    - [./LCL013^3.ax](#lcl0133ax)
    - [./LCL013^4.ax](#lcl0134ax)
    - [./LCL013^5.ax](#lcl0135ax)
    - [./LCL013^6.ax](#lcl0136ax)
    - [./LCL014^0.ax](#lcl0140ax)
    - [./LCL015^0.ax](#lcl0150ax)
    - [./LCL015^1.ax](#lcl0151ax)
    - [./LCL016^0.ax](#lcl0160ax)
    - [./LCL016^1.ax](#lcl0161ax)
    - [./LCL017^0.ax](#lcl0170ax)
    - [./LCL017^1.ax](#lcl0171ax)
    - [./LDA001-0.ax](#lda001-0ax)
    - [./MAT001^0.ax](#mat0010ax)
    - [./MED001+0.ax](#med0010ax)
    - [./MED001+1.ax](#med0011ax)
    - [./MED002+0.ax](#med0020ax)
    - [./MGT001+0.ax](#mgt0010ax)
    - [./MGT001-0.ax](#mgt001-0ax)
    - [./MSC001-0.ax](#msc001-0ax)
    - [./MSC001-1.ax](#msc001-1ax)
    - [./MSC001-2.ax](#msc001-2ax)
    - [./MVA001-0.ax](#mva001-0ax)
    - [./NLP001+0.ax](#nlp0010ax)
  - [Number Theory](#number-theory)
    - [./NUM001-0.ax](#num001-0ax)
    - [./NUM001-1.ax](#num001-1ax)
    - [./NUM001-2.ax](#num001-2ax)
    - [./NUM002-0.ax](#num002-0ax)
    - [./NUM003-0.ax](#num003-0ax)
    - [./NUM004-0.ax](#num004-0ax)
    - [./NUM005+0.ax](#num0050ax)
    - [./NUM005+1.ax](#num0051ax)
    - [./NUM005+2.ax](#num0052ax)
    - [./NUM006^0.ax](#num0060ax)
    - [./NUM007^0.ax](#num0070ax)
    - [./NUM007^1.ax](#num0071ax)
    - [./NUM007^2.ax](#num0072ax)
    - [./NUM007^3.ax](#num0073ax)
    - [./NUM007^4.ax](#num0074ax)
    - [./NUM008+0.ax](#num0080ax)
    - [./NUM009+0.ax](#num0090ax)
  - [Philosophy](#philosophy)
    - [./PHI001^0.ax](#phi0010ax)
    - [./PHI002+0.ax](#phi0020ax)
    - [./PHI002+1.ax](#phi0021ax)
  - [Planning](#planning)
    - [./PLA001-0.ax](#pla001-0ax)
    - [./PLA001-1.ax](#pla001-1ax)
    - [./PLA002+0.ax](#pla0020ax)
    - [./PRD001+0.ax](#prd0010ax)
  - [Puzzles](#puzzles)
    - [./PUZ001-0.ax](#puz001-0ax)
    - [./PUZ002-0.ax](#puz002-0ax)
    - [./PUZ003-0.ax](#puz003-0ax)
    - [./PUZ004-0.ax](#puz004-0ax)
    - [./PUZ005+0.ax](#puz0050ax)
    - [./PUZ005-0.ax](#puz005-0ax)
    - [./PUZ006+0.ax](#puz0060ax)
  - [Quantales](#quantales)
    - [./QUA001^0.ax](#qua0010ax)
    - [./QUA001^1.ax](#qua0011ax)
  - [Relation Algebra](#relation-algebra)
    - [./REL001+0.ax](#rel0010ax)
    - [./REL001+1.ax](#rel0011ax)
    - [./REL001-0.ax](#rel001-0ax)
    - [./REL001-1.ax](#rel001-1ax)
  - [Ring Theory](#ring-theory)
    - [./RNG001-0.ax](#rng001-0ax)
    - [./RNG002-0.ax](#rng002-0ax)
    - [./RNG003-0.ax](#rng003-0ax)
    - [./RNG004-0.ax](#rng004-0ax)
    - [./RNG005-0.ax](#rng005-0ax)
  - [Robbins Algebra](#robbins-algebra)
    - [./ROB001-0.ax](#rob001-0ax)
    - [./ROB001-1.ax](#rob001-1ax)
  - [Set Theory](#set-theory)
    - [./SET001-0.ax](#set001-0ax)
    - [./SET001-1.ax](#set001-1ax)
    - [./SET001-2.ax](#set001-2ax)
    - [./SET001-3.ax](#set001-3ax)
    - [./SET002-0.ax](#set002-0ax)
    - [./SET003-0.ax](#set003-0ax)
    - [./SET004-0.ax](#set004-0ax)
    - [./SET004-1.ax](#set004-1ax)
    - [./SET005+0.ax](#set0050ax)
    - [./SET006+0.ax](#set0060ax)
    - [./SET006+1.ax](#set0061ax)
    - [./SET006+2.ax](#set0062ax)
    - [./SET006+3.ax](#set0063ax)
    - [./SET006+4.ax](#set0064ax)
    - [./SET008^0.ax](#set0080ax)
    - [./SET008^1.ax](#set0081ax)
    - [./SET008^2.ax](#set0082ax)
    - [./SET009^0.ax](#set0090ax)
  - [Semantic Web](#semantic-web)
    - [./SWB001+0.ax](#swb0010ax)
    - [./SWB002+0.ax](#swb0020ax)
    - [./SWB003+0.ax](#swb0030ax)
    - [./SWB003+1.ax](#swb0031ax)
    - [./SWC001+0.ax](#swc0010ax)
    - [./SWC001-0.ax](#swc001-0ax)
    - [./SWV001-0.ax](#swv001-0ax)
    - [./SWV002-0.ax](#swv002-0ax)
    - [./SWV003+0.ax](#swv0030ax)
    - [./SWV004-0.ax](#swv004-0ax)
    - [./SWV005-0.ax](#swv005-0ax)
    - [./SWV005-1.ax](#swv005-1ax)
    - [./SWV005-2.ax](#swv005-2ax)
    - [./SWV005-3.ax](#swv005-3ax)
    - [./SWV005-4.ax](#swv005-4ax)
    - [./SWV005-5.ax](#swv005-5ax)
    - [./SWV005-6.ax](#swv005-6ax)
    - [./SWV005-7.ax](#swv005-7ax)
    - [./SWV006-0.ax](#swv006-0ax)
    - [./SWV006-1.ax](#swv006-1ax)
    - [./SWV006-2.ax](#swv006-2ax)
    - [./SWV006-3.ax](#swv006-3ax)
    - [./SWV007+0.ax](#swv0070ax)
    - [./SWV007+1.ax](#swv0071ax)
    - [./SWV007+2.ax](#swv0072ax)
    - [./SWV007+3.ax](#swv0073ax)
    - [./SWV007+4.ax](#swv0074ax)
    - [./SWV008^0.ax](#swv0080ax)
    - [./SWV008^1.ax](#swv0081ax)
    - [./SWV008^2.ax](#swv0082ax)
    - [./SWV009+0.ax](#swv0090ax)
    - [./SWV010^0.ax](#swv0100ax)
    - [./SWV011+0.ax](#swv0110ax)
    - [./SWV012+0.ax](#swv0120ax)
    - [./SWV013-0.ax](#swv013-0ax)
    - [./SYN000+0.ax](#syn0000ax)
    - [./SYN000-0.ax](#syn000-0ax)
    - [./SYN000^0.ax](#syn0000ax-1)
    - [./SYN000\_0.ax](#syn000_0ax)
    - [./SYN001-0.ax](#syn001-0ax)
    - [./SYN002+0.ax](#syn0020ax)
    - [./TOP001-0.ax](#top001-0ax)

# Axioms

I took a dump of every axiom file less than 500 lines long. Many are clearly computer generated.
The SET007 is a dump of Mizar definitions. Also automated but somewhat readable
ITP001 is a dump of ITP problems

## Agents

### ./AGT001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : AGT001+0 : TPTP v8.2.0. Released v2.7.0.
% Domain   : Agents
% Axioms   : CPlanT system
% Version  : [Bar03] axioms : Especial.
% English  :

% Refs     : [Bar03] Barta, J. (2003), Email to G. Sutcliffe
% Source   : [Bar03]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   20 (   0 unt;   0 def)
%            Number of atoms       :   98 (   0 equ)
%            Maximal formula atoms :    6 (   4 avg)
%            Number of connectives :   79 (   1   ~;   0   |;  58   &)
%                                         (  14 <=>;   6  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   7 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 2-4 aty)
%            Number of functors    :   47 (  47 usr;  47 con; 0-0 aty)
%            Number of variables   :   35 (  35   !;   0   ?)
% SPC      : 

% Comments : Requires NUM005+0.ax NUM005+1.ax
%------------------------------------------------------------------------------
fof(a1_1,axiom,
    ! [A,C,N,L] :
      ( accept_team(A,L,C,N)
    <=> ( accept_city(A,C)
        & accept_leader(A,L)
        & accept_number(A,N) ) ) ).

fof(a1_2,axiom,
    ! [A,N,M] :
      ( ( accept_number(A,N)
        & less(M,N) )
     => accept_number(A,M) ) ).

fof(a1_3,axiom,
    ! [A,N,M,P] :
      ( ( accept_population(A,P,N)
        & less(M,N) )
     => accept_population(A,P,M) ) ).

fof(a1_4,axiom,
    ! [A,L,C] :
      ( the_agent_in_all_proposed_teams(A,L,C)
     => ( accept_leader(A,L)
        & accept_city(A,C) ) ) ).

fof(a1_5,axiom,
    ! [A,L,C] :
      ( any_agent_in_all_proposed_teams(A,L,C)
     => accept_leader(A,L) ) ).

fof(a1_6,axiom,
    ! [A,L,C] :
      ( the_agent_not_in_any_proposed_teams(A,L,C)
     => ~ ( accept_city(A,C)
          & accept_leader(A,L) ) ) ).

fof(a1_7,axiom,
    ! [A,N] :
      ( min_number_of_proposed_agents(A,N)
     => accept_number(A,N) ) ).

fof(a2_1,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n65)
        & accept_population(A,christian,n20)
        & accept_population(A,muslim,n7)
        & accept_population(A,native,n4)
        & accept_population(A,other,n4) )
    <=> accept_city(A,suffertown) ) ).

fof(a2_2,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n54)
        & accept_population(A,christian,n23)
        & accept_population(A,muslim,n3)
        & accept_population(A,native,n1)
        & accept_population(A,other,n9) )
    <=> accept_city(A,centraltown) ) ).

fof(a2_3,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n30)
        & accept_population(A,christian,n8)
        & accept_population(A,muslim,n60)
        & accept_population(A,native,n1)
        & accept_population(A,other,n1) )
    <=> accept_city(A,sunnysideport) ) ).

fof(a2_4,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n70)
        & accept_population(A,christian,n15)
        & accept_population(A,muslim,n1)
        & accept_population(A,native,n10)
        & accept_population(A,other,n4) )
    <=> accept_city(A,centrallakecity) ) ).

fof(a2_5,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n68)
        & accept_population(A,christian,n16)
        & accept_population(A,muslim,n1)
        & accept_population(A,native,n11)
        & accept_population(A,other,n4) )
    <=> accept_city(A,stjosephburgh) ) ).

fof(a2_6,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n70)
        & accept_population(A,christian,n13)
        & accept_population(A,muslim,n0)
        & accept_population(A,native,n15)
        & accept_population(A,other,n2) )
    <=> accept_city(A,northport) ) ).

fof(a2_7,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n12)
        & accept_population(A,christian,n3)
        & accept_population(A,muslim,n0)
        & accept_population(A,native,n85)
        & accept_population(A,other,n0) )
    <=> accept_city(A,coastvillage) ) ).

fof(a2_8,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n0)
        & accept_population(A,christian,n0)
        & accept_population(A,muslim,n0)
        & accept_population(A,native,n100)
        & accept_population(A,other,n0) )
    <=> accept_city(A,sunsetpoint) ) ).

fof(a2_9,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n75)
        & accept_population(A,christian,n24)
        & accept_population(A,muslim,n1)
        & accept_population(A,native,n0)
        & accept_population(A,other,n0) )
    <=> accept_city(A,towna) ) ).

fof(a2_10,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n75)
        & accept_population(A,christian,n25)
        & accept_population(A,muslim,n0)
        & accept_population(A,native,n0)
        & accept_population(A,other,n0) )
    <=> accept_city(A,citya) ) ).

fof(a2_11,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n70)
        & accept_population(A,christian,n20)
        & accept_population(A,muslim,n8)
        & accept_population(A,native,n0)
        & accept_population(A,other,n2) )
    <=> accept_city(A,townb) ) ).

fof(a2_12,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n78)
        & accept_population(A,christian,n20)
        & accept_population(A,muslim,n1)
        & accept_population(A,native,n0)
        & accept_population(A,other,n1) )
    <=> accept_city(A,cityb) ) ).

fof(a2_13,axiom,
    ! [A] :
      ( ( accept_population(A,atheist,n30)
        & accept_population(A,christian,n0)
        & accept_population(A,muslim,n65)
        & accept_population(A,native,n0)
        & accept_population(A,other,n5) )
    <=> accept_city(A,townc) ) ).

%------------------------------------------------------------------------------

```

### ./AGT001+1.ax

Very long 774

### ./AGT001+2.ax

Very long 1128

## Abstract Algebra

### ./ALG001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : ALG001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Algebra (Abstract)
% Axioms   : Abstract algebra axioms, based on Godel set theory
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   24 (   0 unt;   7 nHn;  17 RR)
%            Number of literals    :   66 (  12 equ;  35 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    9 (   8 usr;   0 prp; 2-4 aty)
%            Number of functors    :   11 (  11 usr;   0 con; 2-4 aty)
%            Number of variables   :   74 (   4 sgn)
% SPC      : 

% Comments : Requires SET003-0.ax
%--------------------------------------------------------------------------
%----Definition of associative system
cnf(associative_system1,axiom,
    ( ~ associative(Xs,Xf)
    | ~ member(X,Xs)
    | ~ member(Y,Xs)
    | ~ member(Z,Xs)
    | apply_to_two_arguments(Xf,apply_to_two_arguments(Xf,X,Y),Z) = apply_to_two_arguments(Xf,X,apply_to_two_arguments(Xf,Y,Z)) ) ).

cnf(associative_system2,axiom,
    ( associative(Xs,Xf)
    | member(f34(Xs,Xf),Xs) ) ).

cnf(associative_system3,axiom,
    ( associative(Xs,Xf)
    | member(f35(Xs,Xf),Xs) ) ).

cnf(associative_system4,axiom,
    ( associative(Xs,Xf)
    | member(f36(Xs,Xf),Xs) ) ).

cnf(associative_system5,axiom,
    ( associative(Xs,Xf)
    | apply_to_two_arguments(Xf,apply_to_two_arguments(Xf,f34(Xs,Xf),f35(Xs,Xf)),f36(Xs,Xf)) != apply_to_two_arguments(Xf,f34(Xs,Xf),apply_to_two_arguments(Xf,f35(Xs,Xf),f36(Xs,Xf))) ) ).

%----Definition of identity (left and right)
cnf(identity1,axiom,
    ( ~ identity(Xs,Xf,Xe)
    | member(Xe,Xs) ) ).

cnf(identity2,axiom,
    ( ~ identity(Xs,Xf,Xe)
    | ~ member(X,Xs)
    | apply_to_two_arguments(Xf,Xe,X) = X ) ).

cnf(identity3,axiom,
    ( ~ identity(Xs,Xf,Xe)
    | ~ member(X,Xs)
    | apply_to_two_arguments(Xf,X,Xe) = X ) ).

cnf(identity4,axiom,
    ( identity(Xs,Xf,Xe)
    | ~ member(Xe,Xs)
    | member(f37(Xs,Xf,Xe),Xs) ) ).

cnf(identity5,axiom,
    ( identity(Xs,Xf,Xe)
    | ~ member(Xe,Xs)
    | apply_to_two_arguments(Xf,Xe,f37(Xs,Xf,Xe)) != f37(Xs,Xf,Xe)
    | apply_to_two_arguments(Xf,f37(Xs,Xf,Xe),Xe) != f37(Xs,Xf,Xe) ) ).

%----Definition of inverse (left and right)
cnf(inverse1,axiom,
    ( ~ inverse(Xs,Xf,Xe,Xg)
    | maps(Xg,Xs,Xs) ) ).

cnf(inverse2,axiom,
    ( ~ inverse(Xs,Xf,Xe,Xg)
    | ~ member(X,Xs)
    | apply_to_two_arguments(Xf,apply(Xg,X),X) = Xe ) ).

cnf(inverse3,axiom,
    ( ~ inverse(Xs,Xf,Xe,Xg)
    | ~ member(X,Xs)
    | apply_to_two_arguments(Xf,X,apply(Xg,X)) = Xe ) ).

cnf(inverse4,axiom,
    ( inverse(Xs,Xf,Xe,Xg)
    | ~ maps(Xg,Xs,Xs)
    | member(f38(Xs,Xf,Xe,Xg),Xs) ) ).

cnf(inverse5,axiom,
    ( inverse(Xs,Xf,Xe,Xg)
    | ~ maps(Xg,Xs,Xs)
    | apply_to_two_arguments(Xf,apply(Xg,f38(Xs,Xf,Xe,Xg)),f38(Xs,Xf,Xe,Xg)) != Xe
    | apply_to_two_arguments(Xf,f38(Xs,Xf,Xe,Xg),apply(Xg,f38(Xs,Xf,Xe,Xg))) != Xe ) ).

%----Definition of group
cnf(group1,axiom,
    ( ~ group(Xs,Xf)
    | closed(Xs,Xf) ) ).

cnf(group2,axiom,
    ( ~ group(Xs,Xf)
    | associative(Xs,Xf) ) ).

cnf(group3,axiom,
    ( ~ group(Xs,Xf)
    | identity(Xs,Xf,f39(Xs,Xf)) ) ).

cnf(group4,axiom,
    ( ~ group(Xs,Xf)
    | inverse(Xs,Xf,f39(Xs,Xf),f40(Xs,Xf)) ) ).

cnf(group5,axiom,
    ( group(Xs,Xf)
    | ~ closed(Xs,Xf)
    | ~ associative(Xs,Xf)
    | ~ identity(Xs,Xf,Xe)
    | ~ inverse(Xs,Xf,Xe,Xg) ) ).

%----Definition of commutative system
cnf(commutes1,axiom,
    ( ~ commutes(Xs,Xf)
    | ~ member(X,Xs)
    | ~ member(Y,Xs)
    | apply_to_two_arguments(Xf,X,Y) = apply_to_two_arguments(Xf,Y,X) ) ).

cnf(commutes2,axiom,
    ( commutes(Xs,Xf)
    | member(f41(Xs,Xf),Xs) ) ).

cnf(commutes3,axiom,
    ( commutes(Xs,Xf)
    | member(f42(Xs,Xf),Xs) ) ).

cnf(commutes4,axiom,
    ( commutes(Xs,Xf)
    | apply_to_two_arguments(Xf,f41(Xs,Xf),f42(Xs,Xf)) != apply_to_two_arguments(Xf,f42(Xs,Xf),f41(Xs,Xf)) ) ).

%--------------------------------------------------------------------------

```

### ./ALG002+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : ALG002+0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Algebra (Median)
% Axioms   : Median algebra axioms
% Version  : [VM05] axioms.
% English  :

% Refs     : [VMURL] Veroff & McCune (URL), First-order Proof of a Median A
% Source   : [VMURL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   4 unt;   0 def)
%            Number of atoms       :    4 (   4 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   12 (  12   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(majority,axiom,
    ! [X,Y] : f(X,X,Y) = X ).

fof(permute1,axiom,
    ! [X,Y,Z] : f(X,Y,Z) = f(Z,X,Y) ).

fof(permute2,axiom,
    ! [X,Y,Z] : f(X,Y,Z) = f(X,Z,Y) ).

fof(associativity,axiom,
    ! [W,X,Y,Z] : f(f(X,W,Y),W,Z) = f(X,W,f(Y,W,Z)) ).

%------------------------------------------------------------------------------

```

### ./ALG002-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : ALG002-0 : TPTP v8.2.0. Released v8.0.0.
% Domain   : Algebra (Median)
% Axioms   : Median algebra axioms
% Version  : [VM05] axioms.
% English  :

% Refs     : [VMURL] Veroff & McCune (URL), First-order Proof of a Median A
% Source   : [VMURL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   4 unt;   0 nHn;   0 RR)
%            Number of literals    :    4 (   4 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   12 (   1 sgn)
% SPC      : 

% Comments : UEQ format.
%------------------------------------------------------------------------------
cnf(majority,axiom,
    f(X,X,Y) = X ).

cnf(permute1,axiom,
    f(X,Y,Z) = f(Z,X,Y) ).

cnf(permute2,axiom,
    f(X,Y,Z) = f(X,Z,Y) ).

cnf(associativity,axiom,
    f(f(X,W,Y),W,Z) = f(X,W,f(Y,W,Z)) ).

%------------------------------------------------------------------------------

```

### ./ALG003^0.ax

Very long 2093

## Analysis

### ./ANA001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : ANA001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Analysis (Limits)
% Axioms   : Analysis (limits) axioms for continuous functions
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   14 (   6 unt;   0 nHn;   9 RR)
%            Number of literals    :   27 (   5 equ;  14 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   1 con; 0-2 aty)
%            Number of variables   :   27 (   0 sgn)
% SPC      : 

% Comments : No natural language descriptions are available.
%          : "Contributed by W.W. Bledsoe in a private correspondence",
%            [MOW76].
%--------------------------------------------------------------------------
%----Axiom 1
cnf(right_identity,axiom,
    add(X,n0) = X ).

cnf(left_identity,axiom,
    add(n0,X) = X ).

cnf(reflexivity_of_less_than,axiom,
    ~ less_than(X,X) ).

%----Less than transitivity
cnf(transitivity_of_less_than,axiom,
    ( ~ less_than(X,Y)
    | ~ less_than(Y,Z)
    | less_than(X,Z) ) ).

%----Axiom 2
cnf(axiom_2_1,axiom,
    ( ~ less_than(n0,X)
    | ~ less_than(n0,Y)
    | less_than(n0,minimum(X,Y)) ) ).

cnf(axiom_2_2,axiom,
    ( ~ less_than(n0,X)
    | ~ less_than(n0,Y)
    | less_than(minimum(X,Y),X) ) ).

cnf(axiom_2_3,axiom,
    ( ~ less_than(n0,X)
    | ~ less_than(n0,Y)
    | less_than(minimum(X,Y),Y) ) ).

%----Axiom 3
cnf(axiom_3,axiom,
    ( ~ less_than(X,half(Xa))
    | ~ less_than(Y,half(Xa))
    | less_than(add(X,Y),Xa) ) ).

%----Axiom 4
cnf(c_17,axiom,
    ( ~ less_than(add(absolute(X),absolute(Y)),Xa)
    | less_than(absolute(add(X,Y)),Xa) ) ).

%----Axiom 5
cnf(axiom_5,axiom,
    add(add(X,Y),Z) = add(X,add(Y,Z)) ).

%----Axiom 6
cnf(axiom_6_1,axiom,
    add(X,Y) = add(Y,X) ).

cnf(axiom_6_2,axiom,
    ( ~ less_than(n0,Xa)
    | less_than(n0,half(Xa)) ) ).

%----Axiom 7
cnf(axiom_7,axiom,
    ( ~ less_than(n0,Xa)
    | less_than(n0,half(Xa)) ) ).

%----Axiom 8
cnf(axiom_8,axiom,
    minus(add(X,Y)) = add(minus(X),minus(Y)) ).

%--------------------------------------------------------------------------

```

### ./ANA002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : ANA002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Analysis (Limits)
% Axioms   : Analysis (limits) axioms for continuous functions
% Version  : [Ble90] axioms.
% English  :

% Refs     : [Ble90] Bledsoe (1990), Challenge Problems in Elementary Calcu
%          : [Ble92] Bledsoe (1992), Email to G. Sutcliffe
% Source   : [Ble92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   26 (  11 unt;   2 nHn;  13 RR)
%            Number of literals    :   45 (   6 equ;  17 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-2 aty)
%            Number of variables   :   59 (   4 sgn)
% SPC      : 

% Comments : Based on the theorem in calculus that the sum of two continuous
%            functions is continuous.
%          : Used some ideas from [SETHEO] to format this.
%--------------------------------------------------------------------------
%----|X + Y| <= |X| + |Y|.
%----Clause 8
cnf(absolute_sum_less_or_equal_sum_of_absolutes1,axiom,
    less_or_equal(absolute(add(X,Y)),add(absolute(X),absolute(Y))) ).

%----Clause 8.1
cnf(absolute_sum_less_or_equal_sum_of_absolutes2,axiom,
    ( ~ less_or_equal(add(absolute(X),absolute(Y)),Z)
    | less_or_equal(absolute(add(X,Y)),Z) ) ).

%----Properties of minimum.
%----Clause 9
cnf(minimum1,axiom,
    ( ~ less_or_equal(X,Y)
    | minimum(X,Y) = X ) ).

%----Clause 9.1
cnf(minimum2,axiom,
    less_or_equal(minimum(X,Y),X) ).

%----Clause 9.11
cnf(minimum3,axiom,
    ( ~ less_or_equal(Z,minimum(X,Y))
    | less_or_equal(Z,X) ) ).

%----Clause 9.2
cnf(minimum4,axiom,
    ( ~ less_or_equal(X,Y)
    | less_or_equal(X,minimum(X,Y)) ) ).

%----Clause 10
cnf(minimum5,axiom,
    ( ~ less_or_equal(Y,X)
    | minimum(X,Y) = Y ) ).

%----Clause 10.1
cnf(minimum6,axiom,
    less_or_equal(minimum(X,Y),Y) ).

%----Clause 10.11
cnf(minimum7,axiom,
    ( ~ less_or_equal(Z,minimum(X,Y))
    | less_or_equal(Z,Y) ) ).

%----Clause 10.2
cnf(minimum8,axiom,
    ( ~ less_or_equal(Y,X)
    | less_or_equal(Y,minimum(X,Y)) ) ).

%----Clause 10.3
cnf(minimum9,axiom,
    ( less_or_equal(X,n0)
    | less_or_equal(Y,n0)
    | ~ less_or_equal(minimum(X,Y),n0) ) ).

%----Properties of half.
%----Clause 11
cnf(half_plus_half_is_whole,axiom,
    add(half(X),half(X)) = X ).

%----Clause 11.1
cnf(half_plus_half_less_or_equal_whole,axiom,
    less_or_equal(add(half(X),half(X)),X) ).

%----Clause 11.2
cnf(whole_less_or_equal_half_plus_half,axiom,
    less_or_equal(X,add(half(X),half(X))) ).

%----Clause 11.3
cnf(less_or_equal_sum_of_halves,axiom,
    ( ~ less_or_equal(X,half(Z))
    | ~ less_or_equal(Y,half(Z))
    | less_or_equal(add(X,Y),Z) ) ).

%----Clause 12
cnf(zero_and_half,axiom,
    ( less_or_equal(X,n0)
    | ~ less_or_equal(half(X),n0) ) ).

%----Properties of add.
%----Clause 13
cnf(add_to_both_sides_of_less_equal1,axiom,
    ( ~ less_or_equal(X,Y)
    | less_or_equal(add(X,Z),add(Y,Z)) ) ).

%----Clause 13.1
cnf(add_to_both_sides_of_less_equal2,axiom,
    ( ~ less_or_equal(X,Y)
    | ~ less_or_equal(Z,W)
    | less_or_equal(add(X,Z),add(Y,W)) ) ).

%----Clause 14
cnf(commutativity_of_less_or_equal,axiom,
    ( less_or_equal(X,Y)
    | less_or_equal(Y,X) ) ).

%----Clause 15
cnf(transitivity_of_less_or_equal,axiom,
    ( ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,Z)
    | less_or_equal(X,Z) ) ).

%----Clause 15.1 omitted - it's the same as Clause 15

%----Clause 16
cnf(commutativity_of_add,axiom,
    add(X,Y) = add(Y,X) ).

%----Clause 16_1
cnf(commutativity_of_add_for_less_or_equal,axiom,
    less_or_equal(add(X,Y),add(Y,X)) ).

%----Clause 17
cnf(associativity_of_add,axiom,
    add(add(X,Y),Z) = add(X,add(Y,Z)) ).

%----Clause 17_1
cnf(associativity_of_add_for_less_or_equal1,axiom,
    less_or_equal(add(add(X,Y),Z),add(X,add(Y,Z))) ).

%----Clause 17_2
cnf(associativity_of_add_for_less_or_equal2,axiom,
    less_or_equal(add(X,add(Y,Z)),add(add(X,Y),Z)) ).

%----Clause 18
cnf(equal_implies_less_or_equal,axiom,
    ( X != Y
    | less_or_equal(X,Y) ) ).

%--------------------------------------------------------------------------

```

### ./ANA003-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : ANA003-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Analysis
% Axioms   : A theory of Big-O notation
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : BigO_simp.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   53 (   0 unt;   0 nHn;  15 RR)
%            Number of literals    :  122 (   0 equ;  69 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :   32 (  32 usr;   0 prp; 1-3 aty)
%            Number of functors    :    6 (   6 usr;   0 con; 1-3 aty)
%            Number of variables   :  123 (  30 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax
%------------------------------------------------------------------------------
cnf(cls_SetsAndFunctions_Oset__plus__intro2_0,axiom,
    ( ~ class_HOL_Oplus(T_a)
    | ~ c_in(V_b,V_C,T_a)
    | c_in(c_plus(V_a,V_b,T_a),c_SetsAndFunctions_Oelt__set__plus(V_a,V_C,T_a),T_a) ) ).

cnf(cls_SetsAndFunctions_Oset__plus__intro_0,axiom,
    ( ~ class_HOL_Oplus(T_a)
    | ~ c_in(V_b,V_D,T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_in(c_plus(V_a,V_b,T_a),c_plus(V_C,V_D,tc_set(T_a)),T_a) ) ).

cnf(cls_SetsAndFunctions_Oset__plus__mono2_0,axiom,
    ( ~ class_HOL_Oplus(T_a)
    | ~ c_lessequals(V_E,V_F,tc_set(T_a))
    | ~ c_lessequals(V_C,V_D,tc_set(T_a))
    | c_lessequals(c_plus(V_C,V_E,tc_set(T_a)),c_plus(V_D,V_F,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__plus__mono3_0,axiom,
    ( ~ class_HOL_Oplus(T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_lessequals(c_SetsAndFunctions_Oelt__set__plus(V_a,V_D,T_a),c_plus(V_C,V_D,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__plus__mono4_0,axiom,
    ( ~ class_OrderedGroup_Ocomm__monoid__add(T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_lessequals(c_SetsAndFunctions_Oelt__set__plus(V_a,V_D,T_a),c_plus(V_D,V_C,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__plus__mono_0,axiom,
    ( ~ class_HOL_Oplus(T_a)
    | ~ c_lessequals(V_C,V_D,tc_set(T_a))
    | c_lessequals(c_SetsAndFunctions_Oelt__set__plus(V_a,V_C,T_a),c_SetsAndFunctions_Oelt__set__plus(V_a,V_D,T_a),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__times__intro2_0,axiom,
    ( ~ class_HOL_Otimes(T_a)
    | ~ c_in(V_b,V_C,T_a)
    | c_in(c_times(V_a,V_b,T_a),c_SetsAndFunctions_Oelt__set__times(V_a,V_C,T_a),T_a) ) ).

cnf(cls_SetsAndFunctions_Oset__times__intro_0,axiom,
    ( ~ class_HOL_Otimes(T_a)
    | ~ c_in(V_b,V_D,T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_in(c_times(V_a,V_b,T_a),c_times(V_C,V_D,tc_set(T_a)),T_a) ) ).

cnf(cls_SetsAndFunctions_Oset__times__mono2_0,axiom,
    ( ~ class_HOL_Otimes(T_a)
    | ~ c_lessequals(V_E,V_F,tc_set(T_a))
    | ~ c_lessequals(V_C,V_D,tc_set(T_a))
    | c_lessequals(c_times(V_C,V_E,tc_set(T_a)),c_times(V_D,V_F,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__times__mono3_0,axiom,
    ( ~ class_HOL_Otimes(T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_lessequals(c_SetsAndFunctions_Oelt__set__times(V_a,V_D,T_a),c_times(V_C,V_D,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__times__mono4_0,axiom,
    ( ~ class_OrderedGroup_Ocomm__monoid__mult(T_a)
    | ~ c_in(V_a,V_C,T_a)
    | c_lessequals(c_SetsAndFunctions_Oelt__set__times(V_a,V_D,T_a),c_times(V_D,V_C,tc_set(T_a)),tc_set(T_a)) ) ).

cnf(cls_SetsAndFunctions_Oset__times__mono_0,axiom,
    ( ~ class_HOL_Otimes(T_a)
    | ~ c_lessequals(V_C,V_D,tc_set(T_a))
    | c_lessequals(c_SetsAndFunctions_Oelt__set__times(V_a,V_C,T_a),c_SetsAndFunctions_Oelt__set__times(V_a,V_D,T_a),tc_set(T_a)) ) ).

cnf(clsarity_fun_10,axiom,
    ( class_OrderedGroup_Ocancel__semigroup__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Oab__group__add(T_1) ) ).

cnf(clsarity_fun_11,axiom,
    ( class_OrderedGroup_Ocancel__ab__semigroup__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Oab__group__add(T_1) ) ).

cnf(clsarity_fun_12,axiom,
    ( class_OrderedGroup_Oab__group__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Oab__group__add(T_1) ) ).

cnf(clsarity_fun_13,axiom,
    ( class_OrderedGroup_Osemigroup__mult(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Osemigroup__mult(T_1) ) ).

cnf(clsarity_fun_14,axiom,
    ( class_OrderedGroup_Oab__semigroup__mult(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_fun_15,axiom,
    ( class_OrderedGroup_Omonoid__mult(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_fun_16,axiom,
    ( class_OrderedGroup_Ocomm__monoid__mult(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_fun_17,axiom,
    ( class_Ring__and__Field_Osemiring(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_18,axiom,
    ( class_Ring__and__Field_Ocomm__semiring(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_19,axiom,
    ( class_Ring__and__Field_Osemiring__0(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_2,axiom,
    ( class_HOL_Oplus(tc_fun(T_2,T_1))
    | ~ class_HOL_Oplus(T_1) ) ).

cnf(clsarity_fun_20,axiom,
    ( class_Ring__and__Field_Ocomm__semiring__0(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_21,axiom,
    ( class_Ring__and__Field_Osemiring__0__cancel(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_22,axiom,
    ( class_Ring__and__Field_Oring(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_23,axiom,
    ( class_Ring__and__Field_Ocomm__semiring__0__cancel(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_24,axiom,
    ( class_Ring__and__Field_Ocomm__ring(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_25,axiom,
    ( class_Ring__and__Field_Oaxclass__0__neq__1(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_26,axiom,
    ( class_Ring__and__Field_Osemiring__1(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_27,axiom,
    ( class_Ring__and__Field_Ocomm__semiring__1(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_28,axiom,
    ( class_Ring__and__Field_Osemiring__1__cancel(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_29,axiom,
    ( class_Ring__and__Field_Oring__1(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_3,axiom,
    ( class_HOL_Otimes(tc_fun(T_2,T_1))
    | ~ class_HOL_Otimes(T_1) ) ).

cnf(clsarity_fun_30,axiom,
    ( class_Ring__and__Field_Ocomm__semiring__1__cancel(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_31,axiom,
    ( class_Ring__and__Field_Ocomm__ring__1(tc_fun(T_2,T_1))
    | ~ class_Ring__and__Field_Ocomm__ring__1(T_1) ) ).

cnf(clsarity_fun_4,axiom,
    ( class_HOL_Ominus(tc_fun(T_2,T_1))
    | ~ class_HOL_Ominus(T_1) ) ).

cnf(clsarity_fun_5,axiom,
    ( class_HOL_Ozero(tc_fun(T_2,T_1))
    | ~ class_HOL_Ozero(T_1) ) ).

cnf(clsarity_fun_6,axiom,
    ( class_HOL_Oone(tc_fun(T_2,T_1))
    | ~ class_HOL_Oone(T_1) ) ).

cnf(clsarity_fun_7,axiom,
    ( class_OrderedGroup_Osemigroup__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Osemigroup__add(T_1) ) ).

cnf(clsarity_fun_8,axiom,
    ( class_OrderedGroup_Oab__semigroup__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__add(T_1) ) ).

cnf(clsarity_fun_9,axiom,
    ( class_OrderedGroup_Ocomm__monoid__add(tc_fun(T_2,T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__add(T_1) ) ).

cnf(clsarity_set_10,axiom,
    ( class_OrderedGroup_Osemigroup__mult(tc_set(T_1))
    | ~ class_OrderedGroup_Osemigroup__mult(T_1) ) ).

cnf(clsarity_set_11,axiom,
    ( class_OrderedGroup_Oab__semigroup__add(tc_set(T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__add(T_1) ) ).

cnf(clsarity_set_12,axiom,
    ( class_OrderedGroup_Ocomm__monoid__add(tc_set(T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__add(T_1) ) ).

cnf(clsarity_set_13,axiom,
    ( class_OrderedGroup_Oab__semigroup__mult(tc_set(T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_set_14,axiom,
    ( class_OrderedGroup_Omonoid__mult(tc_set(T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_set_15,axiom,
    ( class_OrderedGroup_Ocomm__monoid__mult(tc_set(T_1))
    | ~ class_OrderedGroup_Ocomm__monoid__mult(T_1) ) ).

cnf(clsarity_set_5,axiom,
    ( class_HOL_Oplus(tc_set(T_1))
    | ~ class_HOL_Oplus(T_1) ) ).

cnf(clsarity_set_6,axiom,
    ( class_HOL_Otimes(tc_set(T_1))
    | ~ class_HOL_Otimes(T_1) ) ).

cnf(clsarity_set_7,axiom,
    ( class_HOL_Ozero(tc_set(T_1))
    | ~ class_HOL_Ozero(T_1) ) ).

cnf(clsarity_set_8,axiom,
    ( class_HOL_Oone(tc_set(T_1))
    | ~ class_HOL_Oone(T_1) ) ).

cnf(clsarity_set_9,axiom,
    ( class_OrderedGroup_Osemigroup__add(tc_set(T_1))
    | ~ class_OrderedGroup_Osemigroup__add(T_1) ) ).

%------------------------------------------------------------------------------

```

### ./BIO001+0.ax

Very long 400988

### ./BOO001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : BOO001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Algebra (Ternary Boolean)
% Axioms   : Ternary Boolean algebra (equality) axioms
% Version  : [OTTER] (equality) axioms.
% English  :

% Refs     : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [Win82] Winker (1982), Generation and Verification of Finite M
% Source   : [OTTER]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    5 (   5 unt;   0 nHn;   0 RR)
%            Number of literals    :    5 (   5 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 1-3 aty)
%            Number of variables   :   13 (   2 sgn)
% SPC      : 

% Comments : These axioms appear in [Win82], in which ternary_multiply_1 is
%            shown to be independant.
%          : These axioms are also used in [Wos88], p.222.
%--------------------------------------------------------------------------
cnf(associativity,axiom,
    multiply(multiply(V,W,X),Y,multiply(V,W,Z)) = multiply(V,W,multiply(X,Y,Z)) ).

cnf(ternary_multiply_1,axiom,
    multiply(Y,X,X) = X ).

cnf(ternary_multiply_2,axiom,
    multiply(X,X,Y) = X ).

cnf(left_inverse,axiom,
    multiply(inverse(Y),Y,X) = X ).

cnf(right_inverse,axiom,
    multiply(X,Y,inverse(Y)) = X ).

%--------------------------------------------------------------------------

```

### ./BOO002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : BOO002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Boolean Algebra
% Axioms   : Boolean algebra axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [Whi61] Whitesitt (1961), Boolean Algebra and Its Applications
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   22 (  10 unt;   0 nHn;  12 RR)
%            Number of literals    :   60 (   2 equ;  38 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   82 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(closure_of_addition,axiom,
    sum(X,Y,add(X,Y)) ).

cnf(closure_of_multiplication,axiom,
    product(X,Y,multiply(X,Y)) ).

cnf(commutativity_of_addition,axiom,
    ( ~ sum(X,Y,Z)
    | sum(Y,X,Z) ) ).

cnf(commutativity_of_multiplication,axiom,
    ( ~ product(X,Y,Z)
    | product(Y,X,Z) ) ).

cnf(additive_identity1,axiom,
    sum(additive_identity,X,X) ).

cnf(additive_identity2,axiom,
    sum(X,additive_identity,X) ).

cnf(multiplicative_identity1,axiom,
    product(multiplicative_identity,X,X) ).

cnf(multiplicative_identity2,axiom,
    product(X,multiplicative_identity,X) ).

cnf(distributivity1,axiom,
    ( ~ product(X,Y,V1)
    | ~ product(X,Z,V2)
    | ~ sum(Y,Z,V3)
    | ~ product(X,V3,V4)
    | sum(V1,V2,V4) ) ).

cnf(distributivity2,axiom,
    ( ~ product(X,Y,V1)
    | ~ product(X,Z,V2)
    | ~ sum(Y,Z,V3)
    | ~ sum(V1,V2,V4)
    | product(X,V3,V4) ) ).

cnf(distributivity3,axiom,
    ( ~ product(Y,X,V1)
    | ~ product(Z,X,V2)
    | ~ sum(Y,Z,V3)
    | ~ product(V3,X,V4)
    | sum(V1,V2,V4) ) ).

cnf(distributivity4,axiom,
    ( ~ product(Y,X,V1)
    | ~ product(Z,X,V2)
    | ~ sum(Y,Z,V3)
    | ~ sum(V1,V2,V4)
    | product(V3,X,V4) ) ).

cnf(distributivity5,axiom,
    ( ~ sum(X,Y,V1)
    | ~ sum(X,Z,V2)
    | ~ product(Y,Z,V3)
    | ~ sum(X,V3,V4)
    | product(V1,V2,V4) ) ).

cnf(distributivity6,axiom,
    ( ~ sum(X,Y,V1)
    | ~ sum(X,Z,V2)
    | ~ product(Y,Z,V3)
    | ~ product(V1,V2,V4)
    | sum(X,V3,V4) ) ).

cnf(distributivity7,axiom,
    ( ~ sum(Y,X,V1)
    | ~ sum(Z,X,V2)
    | ~ product(Y,Z,V3)
    | ~ sum(V3,X,V4)
    | product(V1,V2,V4) ) ).

cnf(distributivity8,axiom,
    ( ~ sum(Y,X,V1)
    | ~ sum(Z,X,V2)
    | ~ product(Y,Z,V3)
    | ~ product(V1,V2,V4)
    | sum(V3,X,V4) ) ).

cnf(additive_inverse1,axiom,
    sum(inverse(X),X,multiplicative_identity) ).

cnf(additive_inverse2,axiom,
    sum(X,inverse(X),multiplicative_identity) ).

cnf(multiplicative_inverse1,axiom,
    product(inverse(X),X,additive_identity) ).

cnf(multiplicative_inverse2,axiom,
    product(X,inverse(X),additive_identity) ).

%-----Well definedness of the operations
cnf(addition_is_well_defined,axiom,
    ( ~ sum(X,Y,U)
    | ~ sum(X,Y,V)
    | U = V ) ).

cnf(multiplication_is_well_defined,axiom,
    ( ~ product(X,Y,U)
    | ~ product(X,Y,V)
    | U = V ) ).

%--------------------------------------------------------------------------

```

### ./BOO003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : BOO003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Boolean Algebra
% Axioms   : Boolean algebra (equality) axioms
% Version  : [ANL] (equality) axioms.
% English  :

% Refs     :
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   14 (  14 unt;   0 nHn;   0 RR)
%            Number of literals    :   14 (  14 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   24 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(commutativity_of_add,axiom,
    add(X,Y) = add(Y,X) ).

cnf(commutativity_of_multiply,axiom,
    multiply(X,Y) = multiply(Y,X) ).

cnf(distributivity1,axiom,
    add(multiply(X,Y),Z) = multiply(add(X,Z),add(Y,Z)) ).

cnf(distributivity2,axiom,
    add(X,multiply(Y,Z)) = multiply(add(X,Y),add(X,Z)) ).

cnf(distributivity3,axiom,
    multiply(add(X,Y),Z) = add(multiply(X,Z),multiply(Y,Z)) ).

cnf(distributivity4,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(additive_inverse1,axiom,
    add(X,inverse(X)) = multiplicative_identity ).

cnf(additive_inverse2,axiom,
    add(inverse(X),X) = multiplicative_identity ).

cnf(multiplicative_inverse1,axiom,
    multiply(X,inverse(X)) = additive_identity ).

cnf(multiplicative_inverse2,axiom,
    multiply(inverse(X),X) = additive_identity ).

cnf(multiplicative_id1,axiom,
    multiply(X,multiplicative_identity) = X ).

cnf(multiplicative_id2,axiom,
    multiply(multiplicative_identity,X) = X ).

cnf(additive_id1,axiom,
    add(X,additive_identity) = X ).

cnf(additive_id2,axiom,
    add(additive_identity,X) = X ).

%--------------------------------------------------------------------------

```

### ./BOO004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : BOO004-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Boolean Algebra
% Axioms   : Boolean algebra (equality) axioms
% Version  : [Ver94] (equality) axioms.
% English  :

% Refs     : [Ver94] Veroff (1994), Problem Set
% Source   : [Ver94]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   0 RR)
%            Number of literals    :    8 (   8 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   14 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(commutativity_of_add,axiom,
    add(X,Y) = add(Y,X) ).

cnf(commutativity_of_multiply,axiom,
    multiply(X,Y) = multiply(Y,X) ).

cnf(distributivity1,axiom,
    add(X,multiply(Y,Z)) = multiply(add(X,Y),add(X,Z)) ).

cnf(distributivity2,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(additive_id1,axiom,
    add(X,additive_identity) = X ).

cnf(multiplicative_id1,axiom,
    multiply(X,multiplicative_identity) = X ).

cnf(additive_inverse1,axiom,
    add(X,inverse(X)) = multiplicative_identity ).

cnf(multiplicative_inverse1,axiom,
    multiply(X,inverse(X)) = additive_identity ).

%--------------------------------------------------------------------------

```

## Category Theory

### ./CAT001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : CAT001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Category theory
% Axioms   : Category theory axioms
% Version  : [Mit67] axioms.
% English  :

% Refs     : [Mit67] Mitchell (1967), Theory of Categories
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   18 (   6 unt;   0 nHn;  12 RR)
%            Number of literals    :   45 (   1 equ;  27 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   3 usr;   0 prp; 1-3 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   52 (   5 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Notice that composition is read as compose(x,y)(G) means x o y, -i.e.
%----x(y(G)). It is a skolem function from -(all x all
%----y, (DEF(x,y) -> exists z (P(x,y,z)))).

%-----Composition is closed when defined
cnf(closure_of_composition,axiom,
    ( ~ defined(X,Y)
    | product(X,Y,compose(X,Y)) ) ).

%-----Associative property
cnf(associative_property1,axiom,
    ( ~ product(X,Y,Z)
    | defined(X,Y) ) ).

cnf(associative_property2,axiom,
    ( ~ product(X,Y,Xy)
    | ~ defined(Xy,Z)
    | defined(Y,Z) ) ).

%-----Special category theory axiom
cnf(category_theory_axiom1,axiom,
    ( ~ product(X,Y,Xy)
    | ~ product(Y,Z,Yz)
    | ~ defined(Xy,Z)
    | defined(X,Yz) ) ).

cnf(category_theory_axiom2,axiom,
    ( ~ product(X,Y,Xy)
    | ~ product(Xy,Z,Xyz)
    | ~ product(Y,Z,Yz)
    | product(X,Yz,Xyz) ) ).

cnf(category_theory_axiom3,axiom,
    ( ~ product(Y,Z,Yz)
    | ~ defined(X,Yz)
    | defined(X,Y) ) ).

cnf(category_theory_axiom4,axiom,
    ( ~ product(Y,Z,Yz)
    | ~ product(X,Y,Xy)
    | ~ defined(X,Yz)
    | defined(Xy,Z) ) ).

cnf(category_theory_axiom5,axiom,
    ( ~ product(Y,Z,Yz)
    | ~ product(X,Yz,Xyz)
    | ~ product(X,Y,Xy)
    | product(Xy,Z,Xyz) ) ).

cnf(category_theory_axiom6,axiom,
    ( ~ defined(X,Y)
    | ~ defined(Y,Z)
    | ~ identity_map(Y)
    | defined(X,Z) ) ).

%-----Properties of domain(x) and codomain(x)
cnf(domain_is_an_identity_map,axiom,
    identity_map(domain(X)) ).

cnf(codomain_is_an_identity_map,axiom,
    identity_map(codomain(X)) ).

cnf(mapping_from_x_to_its_domain,axiom,
    defined(X,domain(X)) ).

cnf(mapping_from_codomain_of_x_to_x,axiom,
    defined(codomain(X),X) ).

cnf(product_on_domain,axiom,
    product(X,domain(X),X) ).

cnf(product_on_codomain,axiom,
    product(codomain(X),X,X) ).

%-----Definition of the identity predicate
cnf(identity1,axiom,
    ( ~ defined(X,Y)
    | ~ identity_map(X)
    | product(X,Y,Y) ) ).

cnf(identity2,axiom,
    ( ~ defined(X,Y)
    | ~ identity_map(Y)
    | product(X,Y,X) ) ).

%-----Composition is well defined
cnf(composition_is_well_defined,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | Z = W ) ).

%--------------------------------------------------------------------------

```

### ./CAT002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : CAT002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Category theory
% Axioms   : Category theory (equality) axioms
% Version  : [Qua89] (equality) axioms.
% English  :

% Refs     : [Qua89] Quaife (1989), Email to L. Wos
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    7 (   4 unt;   0 nHn;   3 RR)
%            Number of literals    :   11 (  11 equ;   4 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Composition is read right-to-left: compose(x,y)(G) means -y(x(G)) The
%----axioms themselves
cnf(codomain_of_domain_is_domain,axiom,
    codomain(domain(X)) = domain(X) ).

cnf(domain_of_codomain_is_codomain,axiom,
    domain(codomain(X)) = codomain(X) ).

cnf(domain_composition,axiom,
    compose(domain(X),X) = X ).

cnf(codomain_composition,axiom,
    compose(X,codomain(X)) = X ).

cnf(codomain_domain1,axiom,
    ( codomain(X) != domain(Y)
    | domain(compose(X,Y)) = domain(X) ) ).

cnf(codomain_domain2,axiom,
    ( codomain(X) != domain(Y)
    | codomain(compose(X,Y)) = codomain(Y) ) ).

cnf(star_property,axiom,
    ( codomain(X) != domain(Y)
    | codomain(Y) != domain(Z)
    | compose(X,compose(Y,Z)) = compose(compose(X,Y),Z) ) ).

%--------------------------------------------------------------------------

```

### ./CAT003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : CAT003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Category Theory
% Axioms   : Category theory axioms
% Version  : [Sco79] axioms : Reduced > Complete.
% English  :

% Refs     : [Sco79] Scott (1979), Identity and Existence in Intuitionist L
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   17 (   3 unt;   2 nHn;  12 RR)
%            Number of literals    :   37 (  15 equ;  17 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :   31 (   4 sgn)
% SPC      : 

% Comments : Axioms simplified by Art Quaife.
%--------------------------------------------------------------------------
%----Non-standard in that E(x) stands for "x exists", i.e. a system for
%----intuitionistic logic.  Viewed classically, this can be taken
%----as a partitioning of models M into elements of E and other elements
%----of M; then Scott's quantifiers are relativized to range only over
%----E, whereas free variables range over all of M.
%----Quaife has this written: (this looks really weird, but results from
%----having = here stand for equivalence, and it is a strange fact from
%----Scott's conception that all non-existent things are equivalent. all
%----x all y ((x == y) | E(x) | E(y))).

%-----Restricted equality axioms
cnf(equivalence_implies_existence1,axiom,
    ( ~ equivalent(X,Y)
    | there_exists(X) ) ).

cnf(equivalence_implies_existence2,axiom,
    ( ~ equivalent(X,Y)
    | X = Y ) ).

cnf(existence_and_equality_implies_equivalence1,axiom,
    ( ~ there_exists(X)
    | X != Y
    | equivalent(X,Y) ) ).

%-----Category theory axioms
cnf(domain_has_elements,axiom,
    ( ~ there_exists(domain(X))
    | there_exists(X) ) ).

cnf(codomain_has_elements,axiom,
    ( ~ there_exists(codomain(X))
    | there_exists(X) ) ).

cnf(composition_implies_domain,axiom,
    ( ~ there_exists(compose(X,Y))
    | there_exists(domain(X)) ) ).

cnf(domain_codomain_composition1,axiom,
    ( ~ there_exists(compose(X,Y))
    | domain(X) = codomain(Y) ) ).

cnf(domain_codomain_composition2,axiom,
    ( ~ there_exists(domain(X))
    | domain(X) != codomain(Y)
    | there_exists(compose(X,Y)) ) ).

cnf(associativity_of_compose,axiom,
    compose(X,compose(Y,Z)) = compose(compose(X,Y),Z) ).

cnf(compose_domain,axiom,
    compose(X,domain(X)) = X ).

cnf(compose_codomain,axiom,
    compose(codomain(X),X) = X ).

%-----Axioms from Scott proven dependant by Quaife (with OTTER)

%-----Restricted equality axioms
cnf(equivalence_implies_existence3,axiom,
    ( ~ equivalent(X,Y)
    | there_exists(Y) ) ).

cnf(existence_and_equality_implies_equivalence2,axiom,
    ( ~ there_exists(X)
    | ~ there_exists(Y)
    | X != Y
    | equivalent(X,Y) ) ).

%-----Category theory axioms
cnf(composition_implies_codomain,axiom,
    ( ~ there_exists(compose(X,Y))
    | there_exists(codomain(X)) ) ).

%-----Axiom of indiscernibles
cnf(indiscernibles1,axiom,
    ( there_exists(f1(X,Y))
    | X = Y ) ).

cnf(indiscernibles2,axiom,
    ( X = f1(X,Y)
    | Y = f1(X,Y)
    | X = Y ) ).

cnf(indiscernibles3,axiom,
    ( X != f1(X,Y)
    | Y != f1(X,Y)
    | X = Y ) ).

%----definition of functor: morphisms of categories; i.e. functions -that
%----are strict :    E(f(x)) -> E(x).
%-----         total :     E(x) -> E(f(x)).
%-----         preserving: f(dom(x)) = dom(f(x)).
%-----                     f(cod(x)) = cod(f(x)).
%-----             E(star(x,y)) -> (f(star(x,y)) = star(f(x),f(y))).
%--------------------------------------------------------------------------

```

### ./CAT004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : CAT004-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Category Theory
% Axioms   : Category theory axioms
% Version  : [Sco79] axioms : Reduced > Complete.
% English  :

% Refs     : [Sco79] Scott (1979), Identity and Existence in Intuitionist L
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   3 unt;   0 nHn;   8 RR)
%            Number of literals    :   21 (   7 equ;  10 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   19 (   2 sgn)
% SPC      : 

% Comments : The dependent axioms have been removed.
%--------------------------------------------------------------------------
%----Non-standard in that E(x) stands for "x exists", i.e. a system -for
%----intuitionistic logic.  Viewed classically, this can be -taken
%----as a partitioning of models M into elements of E and -other elements
%----of M; then Scott's quantifiers are relativized -to range only over
%----E, whereas free variables range over all of -M.
%----Quaife has this written: (this looks really weird, but results -from
%----having = here stand for equivalence, and it is a strange -fact from
%----Scott's conception that all non-existent things are -equivalent. all
%----x all y ((x = y) | E(x) | E(y))).

%-----Restricted equality axioms
cnf(equivalence_implies_existence1,axiom,
    ( ~ equivalent(X,Y)
    | there_exists(X) ) ).

cnf(equivalence_implies_existence2,axiom,
    ( ~ equivalent(X,Y)
    | X = Y ) ).

cnf(existence_and_equality_implies_equivalence1,axiom,
    ( ~ there_exists(X)
    | X != Y
    | equivalent(X,Y) ) ).

%-----Category theory axioms
cnf(domain_has_elements,axiom,
    ( ~ there_exists(domain(X))
    | there_exists(X) ) ).

cnf(codomain_has_elements,axiom,
    ( ~ there_exists(codomain(X))
    | there_exists(X) ) ).

cnf(composition_implies_domain,axiom,
    ( ~ there_exists(compose(X,Y))
    | there_exists(domain(X)) ) ).

cnf(domain_codomain_composition1,axiom,
    ( ~ there_exists(compose(X,Y))
    | domain(X) = codomain(Y) ) ).

cnf(domain_codomain_composition2,axiom,
    ( ~ there_exists(domain(X))
    | domain(X) != codomain(Y)
    | there_exists(compose(X,Y)) ) ).

cnf(associativity_of_compose,axiom,
    compose(X,compose(Y,Z)) = compose(compose(X,Y),Z) ).

cnf(compose_domain,axiom,
    compose(X,domain(X)) = X ).

cnf(compose_codomain,axiom,
    compose(codomain(X),X) = X ).

%--------------------------------------------------------------------------

```

## Combinatory Logic

### ./COL001-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : COL001-0 : TPTP v8.2.0. Bugfixed v1.2.0.
% Domain   : Combinatory Logic
% Axioms   : Type-respecting combinators
% Version  : [Jec95] (equality) axioms.
% English  :

% Refs     : [Jec95] Jech (1995), Otter Experiments in a System of Combinat
% Source   : [Jec95]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   10 (   8 unt;   1 nHn;   2 RR)
%            Number of literals    :   12 (  12 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   4 con; 0-2 aty)
%            Number of variables   :   18 (   3 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
cnf(k_definition,axiom,
    apply(k(X),Y) = X ).

cnf(projection1,axiom,
    apply(projection1,pair(X,Y)) = X ).

cnf(projection2,axiom,
    apply(projection2,pair(X,Y)) = Y ).

cnf(pairing,axiom,
    pair(apply(projection1,X),apply(projection2,X)) = X ).

cnf(pairwise_application,axiom,
    apply(pair(X,Y),Z) = pair(apply(X,Z),apply(Y,Z)) ).

cnf(abstraction,axiom,
    apply(apply(apply(abstraction,X),Y),Z) = apply(apply(X,k(Z)),apply(Y,Z)) ).

cnf(equality,axiom,
    apply(eq,pair(X,X)) = projection1 ).

cnf(extensionality1,axiom,
    ( X = Y
    | apply(eq,pair(X,Y)) = projection2 ) ).

cnf(extensionality2,axiom,
    ( X = Y
    | apply(X,n(X,Y)) != apply(Y,n(X,Y)) ) ).

cnf(different_projections,axiom,
    projection1 != projection2 ).

%------------------------------------------------------------------------------

```

### ./COL002-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : COL002-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Combinatory Logic
% Axioms   : Combinators
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Comb.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   25 (  11 unt;   8 nHn;  21 RR)
%            Number of literals    :   63 (  35 equ;  23 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   13 (  13 usr;   5 con; 0-4 aty)
%            Number of variables   :   58 (  16 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax
%------------------------------------------------------------------------------
cnf(cls_Comb_OAp__contractE_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,v_sko__uR_H(V_p,V_q,V_r))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uR8(V_p,V_q,V_r)),v_sko__uR9(V_p,V_q,V_r))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uR__(V_p,V_q,V_r),V_q) ) ).

cnf(cls_Comb_OAp__contractE_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uR_H(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uR8(V_p,V_q,V_r)),v_sko__uR9(V_p,V_q,V_r))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uR__(V_p,V_q,V_r),V_q) ) ).

cnf(cls_Comb_OAp__contractE_2,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uR__(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,v_sko__uR_H(V_p,V_q,V_r))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uR8(V_p,V_q,V_r)),v_sko__uR9(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__contractE_3,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uR_H(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uR__(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uR8(V_p,V_q,V_r)),v_sko__uR9(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__contractE_4,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,v_sko__uR_H(V_p,V_q,V_r))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uR8(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uR9(V_p,V_q,V_r),V_q))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uR__(V_p,V_q,V_r),V_q) ) ).

cnf(cls_Comb_OAp__contractE_5,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uR_H(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uR8(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uR9(V_p,V_q,V_r),V_q))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uR__(V_p,V_q,V_r),V_q) ) ).

cnf(cls_Comb_OAp__contractE_6,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uR__(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,v_sko__uR_H(V_p,V_q,V_r))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uR8(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uR9(V_p,V_q,V_r),V_q)) ) ).

cnf(cls_Comb_OAp__contractE_7,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uR_H(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uR__(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uR8(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uR9(V_p,V_q,V_r),V_q)) ) ).

cnf(cls_Comb_OI__contract__E_0,axiom,
    ~ c_in(c_Pair(c_Comb_OI,V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_OK1__contractD_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_z = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,v_sko__uR7(V_x,V_z)) ) ).

cnf(cls_Comb_OK1__contractD_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_x,v_sko__uR7(V_x,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OK__contractE_0,axiom,
    ~ c_in(c_Pair(c_Comb_Ocomb_OK,V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_OS__contractE_0,axiom,
    ~ c_in(c_Pair(c_Comb_Ocomb_OS,V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Ocomb_Odistinct__1__iff1_0,axiom,
    c_Comb_Ocomb_OK != c_Comb_Ocomb_OS ).

cnf(cls_Comb_Ocomb_Odistinct__2__iff1_0,axiom,
    c_Comb_Ocomb_OS != c_Comb_Ocomb_OK ).

cnf(cls_Comb_Ocomb_Odistinct__3__iff1_0,axiom,
    c_Comb_Ocomb_OK != c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H) ).

cnf(cls_Comb_Ocomb_Odistinct__4__iff1_0,axiom,
    c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H) != c_Comb_Ocomb_OK ).

cnf(cls_Comb_Ocomb_Odistinct__5__iff1_0,axiom,
    c_Comb_Ocomb_OS != c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H) ).

cnf(cls_Comb_Ocomb_Odistinct__6__iff1_0,axiom,
    c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H) != c_Comb_Ocomb_OS ).

cnf(cls_Comb_Ocomb_Oinject__iff1_0,axiom,
    ( c_Comb_Ocomb_Oop_A_D_D(V_comb1,V_comb2) != c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H)
    | V_comb1 = V_comb1_H ) ).

cnf(cls_Comb_Ocomb_Oinject__iff1_1,axiom,
    ( c_Comb_Ocomb_Oop_A_D_D(V_comb1,V_comb2) != c_Comb_Ocomb_Oop_A_D_D(V_comb1_H,V_comb2_H)
    | V_comb2 = V_comb2_H ) ).

cnf(cls_Comb_Ocontract_OAp1_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_Ocontract_OAp2_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_z,V_x),c_Comb_Ocomb_Oop_A_D_D(V_z,V_y),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_Ocontract_OK_0,axiom,
    c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_y),V_x,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Ocontract_OS_0,axiom,
    c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_y),V_z),c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_z)),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

%------------------------------------------------------------------------------

```

### ./COL002-1.ax

```vampire
%------------------------------------------------------------------------------
% File     : COL002-1 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Combinatory Logic
% Axioms   : Combinators
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Comb2.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   21 (   3 unt;   6 nHn;  16 RR)
%            Number of literals    :   58 (  25 equ;  19 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   17 (  17 usr;   5 con; 0-4 aty)
%            Number of variables   :   53 (   1 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax, COL002-0.ax
%------------------------------------------------------------------------------
cnf(cls_Comb_OAp__parcontractE_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uTF(V_p,V_q,V_r)),v_sko__uTG(V_p,V_q,V_r))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uTI(V_p,V_q,V_r),v_sko__uTH(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__parcontractE_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uTH(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uTF(V_p,V_q,V_r)),v_sko__uTG(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__parcontractE_2,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uTI(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uTF(V_p,V_q,V_r)),v_sko__uTG(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__parcontractE_3,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uTF(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uTG(V_p,V_q,V_r),V_q))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(v_sko__uTI(V_p,V_q,V_r),v_sko__uTH(V_p,V_q,V_r)) ) ).

cnf(cls_Comb_OAp__parcontractE_4,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_q,v_sko__uTH(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uTF(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uTG(V_p,V_q,V_r),V_q)) ) ).

cnf(cls_Comb_OAp__parcontractE_5,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_p,V_q),V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_p,v_sko__uTI(V_p,V_q,V_r),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_Oop_A_D_D(V_p,V_q)
    | V_p = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_r)
    | V_r = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(v_sko__uTF(V_p,V_q,V_r),V_q),c_Comb_Ocomb_Oop_A_D_D(v_sko__uTG(V_p,V_q,V_r),V_q)) ) ).

cnf(cls_Comb_OAp__reduce1_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OAp__reduce2_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_z,V_x),c_Comb_Ocomb_Oop_A_D_D(V_z,V_y),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OK1__parcontractD__dest_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_z = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,v_sko__uTE(V_x,V_z)) ) ).

cnf(cls_Comb_OK1__parcontractD__dest_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_x,v_sko__uTE(V_x,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OK__parcontractE_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_OK,V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_OK ) ).

cnf(cls_Comb_OS1__parcontractD__dest_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_z = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uTD(V_x,V_z)) ) ).

cnf(cls_Comb_OS1__parcontractD__dest_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_x,v_sko__uTD(V_x,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OS2__parcontractD__dest_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_y),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_z = c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,v_sko__uTB(V_x,V_y,V_z)),v_sko__uTC(V_x,V_y,V_z)) ) ).

cnf(cls_Comb_OS2__parcontractD__dest_1,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_y),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_x,v_sko__uTB(V_x,V_y,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OS2__parcontractD__dest_2,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_y),V_z,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(V_y,v_sko__uTC(V_x,V_y,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Comb_OS__parcontractE_0,axiom,
    ( ~ c_in(c_Pair(c_Comb_Ocomb_OS,V_r,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | V_r = c_Comb_Ocomb_OS ) ).

cnf(cls_Comb_Oparcontract_Ointros__1_0,axiom,
    c_in(c_Pair(V_x,V_x,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Oparcontract_Ointros__2_0,axiom,
    c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OK,V_x),V_y),V_x,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Oparcontract_Ointros__3_0,axiom,
    c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_OS,V_x),V_y),V_z),c_Comb_Ocomb_Oop_A_D_D(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_z)),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Oparcontract_Ointros__4_0,axiom,
    ( ~ c_in(c_Pair(V_z,V_w,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_w),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Oparcontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

%------------------------------------------------------------------------------

```

## Computing Theory

### ./COM001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : COM001+0 : TPTP v8.2.0. Released v6.4.0.
% Domain   : Computing Theory
% Axioms   : Common axioms for progress/preservation proof
% Version  : [Gre15] axioms : Especial.
% English  :

% Refs     : [Pie02] Pierce (2002), Programming Languages
%          : [Gre15] Grewe (2015), Email to Geoff Sutcliffe
%          : [GE+15] Grewe et al. (2015), Type Systems for the Masses: Deri
% Source   : [Gre15]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   54 (   6 unt;   0 def)
%            Number of atoms       :  285 ( 227 equ)
%            Maximal formula atoms :   33 (   5 avg)
%            Number of connectives :  267 (  36   ~;  17   |; 120   &)
%                                         (   0 <=>;  94  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   23 (   9 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    7 (   5 usr;   1 prp; 0-3 aty)
%            Number of functors    :   16 (  16 usr;   3 con; 0-3 aty)
%            Number of variables   :  307 ( 239   !;  68   ?)
% SPC      :

% Comments : 
%------------------------------------------------------------------------------
fof('EQ-var',axiom,
    ! [VVar0,VVar1] :
      ( ( vvar(VVar0) = vvar(VVar1)
       => VVar0 = VVar1 )
      & ( VVar0 = VVar1
       => vvar(VVar0) = vvar(VVar1) ) ) ).

fof('EQ-abs',axiom,
    ! [VVar0,VTyp0,VExp0,VVar1,VTyp1,VExp1] :
      ( ( vabs(VVar0,VTyp0,VExp0) = vabs(VVar1,VTyp1,VExp1)
       => ( VVar0 = VVar1
          & VTyp0 = VTyp1
          & VExp0 = VExp1 ) )
      & ( ( VVar0 = VVar1
          & VTyp0 = VTyp1
          & VExp0 = VExp1 )
       => vabs(VVar0,VTyp0,VExp0) = vabs(VVar1,VTyp1,VExp1) ) ) ).

fof('EQ-app',axiom,
    ! [VExp0,VExp1,VExp2,VExp3] :
      ( ( vapp(VExp0,VExp1) = vapp(VExp2,VExp3)
       => ( VExp0 = VExp2
          & VExp1 = VExp3 ) )
      & ( ( VExp0 = VExp2
          & VExp1 = VExp3 )
       => vapp(VExp0,VExp1) = vapp(VExp2,VExp3) ) ) ).

fof('DIFF-var-abs',axiom,
    ! [VVar0,VVar1,VTyp0,VExp0] : vvar(VVar0) != vabs(VVar1,VTyp0,VExp0) ).

fof('DIFF-var-app',axiom,
    ! [VVar0,VExp0,VExp1] : vvar(VVar0) != vapp(VExp0,VExp1) ).

fof('DIFF-abs-app',axiom,
    ! [VVar0,VTyp0,VExp0,VExp1,VExp2] : vabs(VVar0,VTyp0,VExp0) != vapp(VExp1,VExp2) ).

fof(isValue0,axiom,
    ! [Vx,VS,Ve,VExp0] :
      ( VExp0 = vabs(Vx,VS,Ve)
     => visValue(VExp0) ) ).

fof(isValue1,axiom,
    ! [Vx,VExp0] :
      ( VExp0 = vvar(Vx)
     => ~ visValue(VExp0) ) ).

fof(isValue2,axiom,
    ! [Ve1,Ve2,VExp0] :
      ( VExp0 = vapp(Ve1,Ve2)
     => ~ visValue(VExp0) ) ).

fof(isFreeVar0,axiom,
    ! [VVar0,VExp0,Vx,Vv] :
      ( ( VVar0 = Vv
        & VExp0 = vvar(Vx) )
     => ( ( Vx = Vv
         => visFreeVar(VVar0,VExp0) )
        & ( visFreeVar(VVar0,VExp0)
         => Vx = Vv ) ) ) ).

fof(isFreeVar1,axiom,
    ! [VT,VVar0,VExp0,Vx,Vv,Ve] :
      ( ( VVar0 = Vv
        & VExp0 = vabs(Vx,VT,Ve) )
     => ( ( ( Vx != Vv
            & visFreeVar(Vv,Ve) )
         => visFreeVar(VVar0,VExp0) )
        & ( visFreeVar(VVar0,VExp0)
         => ( Vx != Vv
            & visFreeVar(Vv,Ve) ) ) ) ) ).

fof(isFreeVar2,axiom,
    ! [VVar0,VExp0,Ve1,Vv,Ve2] :
      ( ( VVar0 = Vv
        & VExp0 = vapp(Ve1,Ve2) )
     => ( ( ( visFreeVar(Vv,Ve1)
            | visFreeVar(Vv,Ve2) )
         => visFreeVar(VVar0,VExp0) )
        & ( visFreeVar(VVar0,VExp0)
         => ( visFreeVar(Vv,Ve1)
            | visFreeVar(Vv,Ve2) ) ) ) ) ).

fof('EQ-empty',axiom,
    ( ( vempty = vempty
     => $true )
    & ( $true
     => vempty = vempty ) ) ).

fof('EQ-bind',axiom,
    ! [VVar0,VTyp0,VCtx0,VVar1,VTyp1,VCtx1] :
      ( ( vbind(VVar0,VTyp0,VCtx0) = vbind(VVar1,VTyp1,VCtx1)
       => ( VVar0 = VVar1
          & VTyp0 = VTyp1
          & VCtx0 = VCtx1 ) )
      & ( ( VVar0 = VVar1
          & VTyp0 = VTyp1
          & VCtx0 = VCtx1 )
       => vbind(VVar0,VTyp0,VCtx0) = vbind(VVar1,VTyp1,VCtx1) ) ) ).

fof('EQ-noType',axiom,
    ( ( vnoType = vnoType
     => $true )
    & ( $true
     => vnoType = vnoType ) ) ).

fof('EQ-someType',axiom,
    ! [VTyp0,VTyp1] :
      ( ( vsomeType(VTyp0) = vsomeType(VTyp1)
       => VTyp0 = VTyp1 )
      & ( VTyp0 = VTyp1
       => vsomeType(VTyp0) = vsomeType(VTyp1) ) ) ).

fof('DIFF-empty-bind',axiom,
    ! [VVar0,VTyp0,VCtx0] : vempty != vbind(VVar0,VTyp0,VCtx0) ).

fof('DIFF-noType-someType',axiom,
    ! [VTyp0] : vnoType != vsomeType(VTyp0) ).

fof(isSomeType0,axiom,
    ! [VOptTyp0] :
      ( VOptTyp0 = vnoType
     => ~ visSomeType(VOptTyp0) ) ).

fof(isSomeType1,axiom,
    ! [Ve,VOptTyp0] :
      ( VOptTyp0 = vsomeType(Ve)
     => visSomeType(VOptTyp0) ) ).

fof(getSomeType0,axiom,
    ! [VOptTyp0,RESULT,Ve] :
      ( VOptTyp0 = vsomeType(Ve)
     => ( RESULT = vgetSomeType(VOptTyp0)
       => RESULT = Ve ) ) ).

fof(lookup0,axiom,
    ! [Vx,VVar0,VCtx0,RESULT] :
      ( ( VVar0 = Vx
        & VCtx0 = vempty )
     => ( RESULT = vlookup(VVar0,VCtx0)
       => RESULT = vnoType ) ) ).

fof(lookup1,axiom,
    ! [VC,Vx,Vy,VVar0,VCtx0,RESULT,VTy] :
      ( ( VVar0 = Vx
        & VCtx0 = vbind(Vy,VTy,VC) )
     => ( Vx = Vy
       => ( RESULT = vlookup(VVar0,VCtx0)
         => RESULT = vsomeType(VTy) ) ) ) ).

fof(lookup2,axiom,
    ! [VTy,Vy,VVar0,VCtx0,RESULT,Vx,VC] :
      ( ( VVar0 = Vx
        & VCtx0 = vbind(Vy,VTy,VC) )
     => ( Vx != Vy
       => ( RESULT = vlookup(VVar0,VCtx0)
         => RESULT = vlookup(Vx,VC) ) ) ) ).

fof('lookup-INV',axiom,
    ! [VVar0,VCtx0,RESULT] :
      ( vlookup(VVar0,VCtx0) = RESULT
     => ( ? [Vx] :
            ( VVar0 = Vx
            & VCtx0 = vempty
            & RESULT = vnoType )
        | ? [VC,Vx,Vy,VTy] :
            ( VVar0 = Vx
            & VCtx0 = vbind(Vy,VTy,VC)
            & Vx = Vy
            & RESULT = vsomeType(VTy) )
        | ? [VTy,Vy,Vx,VC] :
            ( VVar0 = Vx
            & VCtx0 = vbind(Vy,VTy,VC)
            & Vx != Vy
            & RESULT = vlookup(Vx,VC) ) ) ) ).

fof('T-Context-Duplicate',axiom,
    ! [Vy,VTy,Vx,VTx,VC,Ve,VT] :
      ( ( Vx = Vy
        & vtcheck(vbind(Vx,VTx,vbind(Vy,VTy,VC)),Ve,VT) )
     => vtcheck(vbind(Vx,VTx,VC),Ve,VT) ) ).

fof('T-Context-Swap',axiom,
    ! [Vy,VTy,Vx,VTx,VC,Ve,VT] :
      ( ( Vx != Vy
        & vtcheck(vbind(Vx,VTx,vbind(Vy,VTy,VC)),Ve,VT) )
     => vtcheck(vbind(Vy,VTy,vbind(Vx,VTx,VC)),Ve,VT) ) ).

fof('gensym-is-fresh',axiom,
    ! [Vv,Ve] :
      ( vgensym(Ve) = Vv
     => ~ visFreeVar(Vv,Ve) ) ).

fof(subst0,axiom,
    ! [Vx,Vy,VVar0,VExp0,VExp1,RESULT,Ve] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vvar(Vy) )
     => ( Vx = Vy
       => ( RESULT = vsubst(VVar0,VExp0,VExp1)
         => RESULT = Ve ) ) ) ).

fof(subst1,axiom,
    ! [Ve,Vx,VVar0,VExp0,VExp1,RESULT,Vy] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vvar(Vy) )
     => ( Vx != Vy
       => ( RESULT = vsubst(VVar0,VExp0,VExp1)
         => RESULT = vvar(Vy) ) ) ) ).

fof(subst2,axiom,
    ! [VVar0,VExp0,VExp1,RESULT,Ve1,Vx,Ve,Ve2] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vapp(Ve1,Ve2) )
     => ( RESULT = vsubst(VVar0,VExp0,VExp1)
       => RESULT = vapp(vsubst(Vx,Ve,Ve1),vsubst(Vx,Ve,Ve2)) ) ) ).

fof(subst3,axiom,
    ! [Ve,Vx,VVar0,VExp0,VExp1,RESULT,Vy,VT,Ve1] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vabs(Vy,VT,Ve1) )
     => ( Vx = Vy
       => ( RESULT = vsubst(VVar0,VExp0,VExp1)
         => RESULT = vabs(Vy,VT,Ve1) ) ) ) ).

fof(subst4,axiom,
    ! [VVar0,VExp0,VExp1,RESULT,Vx,Ve,VT,Vy,Vfresh,Ve1] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vabs(Vy,VT,Ve1) )
     => ( ( Vx != Vy
          & visFreeVar(Vy,Ve)
          & Vfresh = vgensym(vapp(vapp(Ve,Ve1),vvar(Vx))) )
       => ( RESULT = vsubst(VVar0,VExp0,VExp1)
         => RESULT = vsubst(Vx,Ve,vabs(Vfresh,VT,vsubst(Vy,vvar(Vfresh),Ve1))) ) ) ) ).

fof(subst5,axiom,
    ! [VVar0,VExp0,VExp1,RESULT,Vy,VT,Vx,Ve,Ve1] :
      ( ( VVar0 = Vx
        & VExp0 = Ve
        & VExp1 = vabs(Vy,VT,Ve1) )
     => ( ( Vx != Vy
          & ~ visFreeVar(Vy,Ve) )
       => ( RESULT = vsubst(VVar0,VExp0,VExp1)
         => RESULT = vabs(Vy,VT,vsubst(Vx,Ve,Ve1)) ) ) ) ).

fof('subst-INV',axiom,
    ! [VVar0,VExp0,VExp1,RESULT] :
      ( vsubst(VVar0,VExp0,VExp1) = RESULT
     => ( ? [Vx,Vy,Ve] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vvar(Vy)
            & Vx = Vy
            & RESULT = Ve )
        | ? [Ve,Vx,Vy] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vvar(Vy)
            & Vx != Vy
            & RESULT = vvar(Vy) )
        | ? [Ve1,Vx,Ve,Ve2] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vapp(Ve1,Ve2)
            & RESULT = vapp(vsubst(Vx,Ve,Ve1),vsubst(Vx,Ve,Ve2)) )
        | ? [Ve,Vx,Vy,VT,Ve1] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vabs(Vy,VT,Ve1)
            & Vx = Vy
            & RESULT = vabs(Vy,VT,Ve1) )
        | ? [Vx,Ve,VT,Vy,Vfresh,Ve1] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vabs(Vy,VT,Ve1)
            & Vx != Vy
            & visFreeVar(Vy,Ve)
            & Vfresh = vgensym(vapp(vapp(Ve,Ve1),vvar(Vx)))
            & RESULT = vsubst(Vx,Ve,vabs(Vfresh,VT,vsubst(Vy,vvar(Vfresh),Ve1))) )
        | ? [Vy,VT,Vx,Ve,Ve1] :
            ( VVar0 = Vx
            & VExp0 = Ve
            & VExp1 = vabs(Vy,VT,Ve1)
            & Vx != Vy
            & ~ visFreeVar(Vy,Ve)
            & RESULT = vabs(Vy,VT,vsubst(Vx,Ve,Ve1)) ) ) ) ).

fof('EQ-noExp',axiom,
    ( ( vnoExp = vnoExp
     => $true )
    & ( $true
     => vnoExp = vnoExp ) ) ).

fof('EQ-someExp',axiom,
    ! [VExp0,VExp1] :
      ( ( vsomeExp(VExp0) = vsomeExp(VExp1)
       => VExp0 = VExp1 )
      & ( VExp0 = VExp1
       => vsomeExp(VExp0) = vsomeExp(VExp1) ) ) ).

fof('DIFF-noExp-someExp',axiom,
    ! [VExp0] : vnoExp != vsomeExp(VExp0) ).

fof(isSomeExp0,axiom,
    ! [VOptExp0] :
      ( VOptExp0 = vnoExp
     => ~ visSomeExp(VOptExp0) ) ).

fof(isSomeExp1,axiom,
    ! [Ve,VOptExp0] :
      ( VOptExp0 = vsomeExp(Ve)
     => visSomeExp(VOptExp0) ) ).

fof(getSomeExp0,axiom,
    ! [VOptExp0,RESULT,Ve] :
      ( VOptExp0 = vsomeExp(Ve)
     => ( RESULT = vgetSomeExp(VOptExp0)
       => RESULT = Ve ) ) ).

fof(reduce0,axiom,
    ! [Vx,VExp0,RESULT] :
      ( VExp0 = vvar(Vx)
     => ( RESULT = vreduce(VExp0)
       => RESULT = vnoExp ) ) ).

fof(reduce1,axiom,
    ! [Vx,VS,Ve,VExp0,RESULT] :
      ( VExp0 = vabs(Vx,VS,Ve)
     => ( RESULT = vreduce(VExp0)
       => RESULT = vnoExp ) ) ).

fof(reduce2,axiom,
    ! [Ve2,VExp0,RESULT,Vx,VS,Ve1,Ve2red] :
      ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
     => ( ( Ve2red = vreduce(Ve2)
          & visSomeExp(Ve2red) )
       => ( RESULT = vreduce(VExp0)
         => RESULT = vsomeExp(vapp(vabs(Vx,VS,Ve1),vgetSomeExp(Ve2red))) ) ) ) ).

fof(reduce3,axiom,
    ! [VS,Ve2red,VExp0,RESULT,Vx,Ve2,Ve1] :
      ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
     => ( ( Ve2red = vreduce(Ve2)
          & ~ visSomeExp(Ve2red)
          & visValue(Ve2) )
       => ( RESULT = vreduce(VExp0)
         => RESULT = vsomeExp(vsubst(Vx,Ve2,Ve1)) ) ) ) ).

fof(reduce4,axiom,
    ! [Vx,VS,Ve1,Ve2red,Ve2,VExp0,RESULT] :
      ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
     => ( ( Ve2red = vreduce(Ve2)
          & ~ visSomeExp(Ve2red)
          & ~ visValue(Ve2) )
       => ( RESULT = vreduce(VExp0)
         => RESULT = vnoExp ) ) ) ).

fof(reduce5,axiom,
    ! [Ve1,VExp0,RESULT,Ve1red,Ve2] :
      ( ( VExp0 = vapp(Ve1,Ve2)
        & ! [VVx0,VVS0,VVe10] : Ve1 != vabs(VVx0,VVS0,VVe10) )
     => ( ( Ve1red = vreduce(Ve1)
          & visSomeExp(Ve1red) )
       => ( RESULT = vreduce(VExp0)
         => RESULT = vsomeExp(vapp(vgetSomeExp(Ve1red),Ve2)) ) ) ) ).

fof(reduce6,axiom,
    ! [Ve2,Ve1,Ve1red,VExp0,RESULT] :
      ( ( VExp0 = vapp(Ve1,Ve2)
        & ! [VVx0,VVS0,VVe10] : Ve1 != vabs(VVx0,VVS0,VVe10) )
     => ( ( Ve1red = vreduce(Ve1)
          & ~ visSomeExp(Ve1red) )
       => ( RESULT = vreduce(VExp0)
         => RESULT = vnoExp ) ) ) ).

fof('reduce-INV',axiom,
    ! [VExp0,RESULT] :
      ( vreduce(VExp0) = RESULT
     => ( ? [Vx] :
            ( VExp0 = vvar(Vx)
            & RESULT = vnoExp )
        | ? [Vx,VS,Ve] :
            ( VExp0 = vabs(Vx,VS,Ve)
            & RESULT = vnoExp )
        | ? [Ve2,Vx,VS,Ve1,Ve2red] :
            ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
            & Ve2red = vreduce(Ve2)
            & visSomeExp(Ve2red)
            & RESULT = vsomeExp(vapp(vabs(Vx,VS,Ve1),vgetSomeExp(Ve2red))) )
        | ? [VS,Ve2red,Vx,Ve2,Ve1] :
            ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
            & Ve2red = vreduce(Ve2)
            & ~ visSomeExp(Ve2red)
            & visValue(Ve2)
            & RESULT = vsomeExp(vsubst(Vx,Ve2,Ve1)) )
        | ? [Vx,VS,Ve1,Ve2red,Ve2] :
            ( VExp0 = vapp(vabs(Vx,VS,Ve1),Ve2)
            & Ve2red = vreduce(Ve2)
            & ~ visSomeExp(Ve2red)
            & ~ visValue(Ve2)
            & RESULT = vnoExp )
        | ? [Ve1,Ve1red,Ve2] :
            ( VExp0 = vapp(Ve1,Ve2)
            & ! [VVx0,VVS0,VVe10] : Ve1 != vabs(VVx0,VVS0,VVe10)
            & Ve1red = vreduce(Ve1)
            & visSomeExp(Ve1red)
            & RESULT = vsomeExp(vapp(vgetSomeExp(Ve1red),Ve2)) )
        | ? [Ve2,Ve1,Ve1red] :
            ( VExp0 = vapp(Ve1,Ve2)
            & ! [VVx0,VVS0,VVe10] : Ve1 != vabs(VVx0,VVS0,VVe10)
            & Ve1red = vreduce(Ve1)
            & ~ visSomeExp(Ve1red)
            & RESULT = vnoExp ) ) ) ).

fof('EQ-arrow',axiom,
    ! [VTyp0,VTyp1,VTyp2,VTyp3] :
      ( ( varrow(VTyp0,VTyp1) = varrow(VTyp2,VTyp3)
       => ( VTyp0 = VTyp2
          & VTyp1 = VTyp3 ) )
      & ( ( VTyp0 = VTyp2
          & VTyp1 = VTyp3 )
       => varrow(VTyp0,VTyp1) = varrow(VTyp2,VTyp3) ) ) ).

fof('T-var',axiom,
    ! [VC,Vx,VT] :
      ( vlookup(Vx,VC) = vsomeType(VT)
     => vtcheck(VC,vvar(Vx),VT) ) ).

fof('T-abs',axiom,
    ! [VC,Vx,Ve,VS,VT] :
      ( vtcheck(vbind(Vx,VS,VC),Ve,VT)
     => vtcheck(VC,vabs(Vx,VS,Ve),varrow(VS,VT)) ) ).

fof('T-app',axiom,
    ! [VS,VC,Ve1,Ve2,VT] :
      ( ( vtcheck(VC,Ve1,varrow(VS,VT))
        & vtcheck(VC,Ve2,VS) )
     => vtcheck(VC,vapp(Ve1,Ve2),VT) ) ).

fof('T-inv',axiom,
    ! [Ve,VT,VC] :
      ( vtcheck(VC,Ve,VT)
     => ( ? [Vx] :
            ( Ve = vvar(Vx)
            & vlookup(Vx,VC) = vsomeType(VT) )
        | ? [Vx,Ve2,VT1,VT2] :
            ( Ve = vabs(Vx,VT1,Ve2)
            & VT = varrow(VT1,VT2)
            & vtcheck(vbind(Vx,VT1,VC),Ve2,VT2) )
        | ? [Ve1,Ve2,VS] :
            ( Ve = vapp(Ve1,Ve2)
            & vtcheck(VC,Ve1,varrow(VS,VT))
            & vtcheck(VC,Ve2,VS) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./COM001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : COM001+1 : TPTP v8.2.0. Released v6.4.0.
% Domain   : Computing Theory
% Axioms   : Common axioms for progress/preservation proof
% Version  : [Gre15] axioms : Especial.
% English  :

% Refs     : [Pie02] Pierce (2002), Programming Languages
%          : [Gre15] Grewe (2015), Email to Geoff Sutcliffe
%          : [GE+15] Grewe et al. (2015), Type Systems for the Masses: Deri
% Source   : [Gre15]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   1 unt;   0 def)
%            Number of atoms       :   14 (   0 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :   11 (   3   ~;   0   |;   3   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   6 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-3 aty)
%            Number of variables   :   17 (  17   !;   0   ?)
% SPC      :

% Comments : Requires COM001+0.ax
%------------------------------------------------------------------------------
fof('alpha-equiv-refl',axiom,
    ! [Ve] : valphaEquivalent(Ve,Ve) ).

fof('alpha-equiv-sym',axiom,
    ! [Ve2,Ve1] :
      ( valphaEquivalent(Ve1,Ve2)
     => valphaEquivalent(Ve2,Ve1) ) ).

fof('alpha-equiv-trans',axiom,
    ! [Ve2,Ve1,Ve3] :
      ( ( valphaEquivalent(Ve1,Ve2)
        & valphaEquivalent(Ve2,Ve3) )
     => valphaEquivalent(Ve1,Ve3) ) ).

fof('alpha-equiv-subst-abs',axiom,
    ! [VS,Vx,Vy,Ve] :
      ( ~ visFreeVar(Vy,Ve)
     => valphaEquivalent(vabs(Vx,VS,Ve),vabs(Vy,VS,vsubst(Vx,vvar(Vy),Ve))) ) ).

fof('alpha-equiv-typing',axiom,
    ! [Ve,VC,Ve1,VT] :
      ( ( vtcheck(VC,Ve,VT)
        & valphaEquivalent(Ve,Ve1) )
     => vtcheck(VC,Ve1,VT) ) ).

fof('alpha-equiv-FreeVar',axiom,
    ! [Ve,Vx,Ve1] :
      ( ( ~ visFreeVar(Vx,Ve)
        & valphaEquivalent(Ve,Ve1) )
     => ~ visFreeVar(Vx,Ve1) ) ).

%------------------------------------------------------------------------------

```

## Commonsense Reasoning

### ./CSR001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : CSR001+0 : TPTP v8.2.0. Released .0.
% Domain   : Commonsense Reasoning
% Axioms   : Standard discrete event calculus axioms
% Version  : [Mue04] axioms : Especial.
% English  :

% Refs     : [Mue04] Mueller (2004), A Tool for Satisfiability-based Common
%          : [MS02]  Miller & Shanahan (2002), Some Alternative Formulation
% Source   : [Mue04]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   12 (   0 unt;   0 def)
%            Number of atoms       :   54 (   0 equ)
%            Maximal formula atoms :    6 (   4 avg)
%            Number of connectives :   56 (  14   ~;   2   |;  28   &)
%                                         (   2 <=>;  10  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (   9 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   11 (  11 usr;   0 prp; 2-4 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :   44 (  36   !;   8   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----DEC1
fof(stoppedin_defn,axiom,
    ! [Time1,Fluent,Time2] :
      ( stoppedIn(Time1,Fluent,Time2)
    <=> ? [Event,Time] :
          ( happens(Event,Time)
          & less(Time1,Time)
          & less(Time,Time2)
          & terminates(Event,Fluent,Time) ) ) ).

%----DEC2
fof(startedin_defn,axiom,
    ! [Time1,Time2,Fluent] :
      ( startedIn(Time1,Fluent,Time2)
    <=> ? [Event,Time] :
          ( happens(Event,Time)
          & less(Time1,Time)
          & less(Time,Time2)
          & initiates(Event,Fluent,Time) ) ) ).

%----DEC3
fof(change_holding,axiom,
    ! [Event,Time,Fluent,Fluent2,Offset] :
      ( ( happens(Event,Time)
        & initiates(Event,Fluent,Time)
        & less(n0,Offset)
        & trajectory(Fluent,Time,Fluent2,Offset)
        & ~ stoppedIn(Time,Fluent,plus(Time,Offset)) )
     => holdsAt(Fluent2,plus(Time,Offset)) ) ).

%----DEC4
fof(antitrajectory,axiom,
    ! [Event,Time1,Fluent1,Time2,Fluent2] :
      ( ( happens(Event,Time1)
        & terminates(Event,Fluent1,Time1)
        & less(n0,Time2)
        & antitrajectory(Fluent1,Time1,Fluent2,Time2)
        & ~ startedIn(Time1,Fluent1,plus(Time1,Time2)) )
     => holdsAt(Fluent2,plus(Time1,Time2)) ) ).

%----DEC5
fof(keep_holding,axiom,
    ! [Fluent,Time] :
      ( ( holdsAt(Fluent,Time)
        & ~ releasedAt(Fluent,plus(Time,n1))
        & ~ ? [Event] :
              ( happens(Event,Time)
              & terminates(Event,Fluent,Time) ) )
     => holdsAt(Fluent,plus(Time,n1)) ) ).

%----DEC6
fof(keep_not_holding,axiom,
    ! [Fluent,Time] :
      ( ( ~ holdsAt(Fluent,Time)
        & ~ releasedAt(Fluent,plus(Time,n1))
        & ~ ? [Event] :
              ( happens(Event,Time)
              & initiates(Event,Fluent,Time) ) )
     => ~ holdsAt(Fluent,plus(Time,n1)) ) ).

%----DEC7
fof(keep_released,axiom,
    ! [Fluent,Time] :
      ( ( releasedAt(Fluent,Time)
        & ~ ? [Event] :
              ( happens(Event,Time)
              & ( initiates(Event,Fluent,Time)
                | terminates(Event,Fluent,Time) ) ) )
     => releasedAt(Fluent,plus(Time,n1)) ) ).

%----DEC8
fof(keep_not_released,axiom,
    ! [Fluent,Time] :
      ( ( ~ releasedAt(Fluent,Time)
        & ~ ? [Event] :
              ( happens(Event,Time)
              & releases(Event,Fluent,Time) ) )
     => ~ releasedAt(Fluent,plus(Time,n1)) ) ).

%----DEC9
fof(happens_holds,axiom,
    ! [Event,Time,Fluent] :
      ( ( happens(Event,Time)
        & initiates(Event,Fluent,Time) )
     => holdsAt(Fluent,plus(Time,n1)) ) ).

%----DEC10
fof(happens_terminates_not_holds,axiom,
    ! [Event,Time,Fluent] :
      ( ( happens(Event,Time)
        & terminates(Event,Fluent,Time) )
     => ~ holdsAt(Fluent,plus(Time,n1)) ) ).

%----DEC11
fof(happens_releases,axiom,
    ! [Event,Time,Fluent] :
      ( ( happens(Event,Time)
        & releases(Event,Fluent,Time) )
     => releasedAt(Fluent,plus(Time,n1)) ) ).

%----DEC12
fof(happens_not_released,axiom,
    ! [Event,Time,Fluent] :
      ( ( happens(Event,Time)
        & ( initiates(Event,Fluent,Time)
          | terminates(Event,Fluent,Time) ) )
     => ~ releasedAt(Fluent,plus(Time,n1)) ) ).

%------------------------------------------------------------------------------

```

### ./CSR001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : CSR001+1 : TPTP v8.2.0. Released .0.
% Domain   : Commonsense Reasoning
% Axioms   : Kitchen sink scenario
% Version  : [Sha97] axioms : Especial.
% English  :

% Refs     : [Sha97] Shanahan (1997), Solving the Frame Problem
% Source   : [Sha97]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   13 (   6 unt;   0 def)
%            Number of atoms       :   39 (  27 equ)
%            Maximal formula atoms :   11 (   3 avg)
%            Number of connectives :   32 (   6   ~;   5   |;  14   &)
%                                         (   5 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   11 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   6 usr;   0 prp; 2-4 aty)
%            Number of functors    :    9 (   9 usr;   7 con; 0-2 aty)
%            Number of variables   :   25 (  22   !;   3   ?)
% SPC      : 

% Comments : Requires CSR001+0.ax
%------------------------------------------------------------------------------
fof(initiates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( initiates(Event,Fluent,Time)
    <=> ( ( Event = tapOn
          & Fluent = filling )
        | ( Event = overflow
          & Fluent = spilling )
        | ? [Height] :
            ( holdsAt(waterLevel(Height),Time)
            & Event = tapOff
            & Fluent = waterLevel(Height) )
        | ? [Height] :
            ( holdsAt(waterLevel(Height),Time)
            & Event = overflow
            & Fluent = waterLevel(Height) ) ) ) ).

fof(terminates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( terminates(Event,Fluent,Time)
    <=> ( ( Event = tapOff
          & Fluent = filling )
        | ( Event = overflow
          & Fluent = filling ) ) ) ).

%----tapOn event releases all waterLevels at all times
fof(releases_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( releases(Event,Fluent,Time)
    <=> ? [Height] :
          ( Event = tapOn
          & Fluent = waterLevel(Height) ) ) ).

fof(happens_all_defn,axiom,
    ! [Event,Time] :
      ( happens(Event,Time)
    <=> ( ( Event = tapOn
          & Time = n0 )
        | ( holdsAt(waterLevel(n3),Time)
          & holdsAt(filling,Time)
          & Event = overflow ) ) ) ).

fof(change_of_waterLevel,axiom,
    ! [Height1,Time,Height2,Offset] :
      ( ( holdsAt(waterLevel(Height1),Time)
        & Height2 = plus(Height1,Offset) )
     => trajectory(filling,Time,waterLevel(Height2),Offset) ) ).

fof(same_waterLevel,axiom,
    ! [Time,Height1,Height2] :
      ( ( holdsAt(waterLevel(Height1),Time)
        & holdsAt(waterLevel(Height2),Time) )
     => Height1 = Height2 ) ).

%----Distinct events
fof(tapOff_not_tapOn,axiom,
    tapOff != tapOn ).

fof(tapOff_not_overflow,axiom,
    tapOff != overflow ).

fof(overflow_not_tapOn,axiom,
    overflow != tapOn ).

%----Distinct fluents
fof(filling_not_waterLevel,axiom,
    ! [X] : filling != waterLevel(X) ).

fof(spilling_not_waterLevel,axiom,
    ! [X] : spilling != waterLevel(X) ).

fof(filling_not_spilling,axiom,
    filling != spilling ).

fof(distinct_waterLevels,axiom,
    ! [X,Y] :
      ( waterLevel(X) = waterLevel(Y)
    <=> X = Y ) ).

%------------------------------------------------------------------------------

```

### ./CSR001+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : CSR001+2 : TPTP v8.2.0. Released .0.
% Domain   : Commonsense Reasoning
% Axioms   : Supermarket trolley scenario
% Version  : [Sha97] axioms : Especial.
% English  :

% Refs     : [Sha97] Shanahan (1997), Solving the Frame Problem
% Source   : [Sha97]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   5 unt;   0 def)
%            Number of atoms       :   43 (  30 equ)
%            Maximal formula atoms :   19 (   5 avg)
%            Number of connectives :   46 (  11   ~;  10   |;  22   &)
%                                         (   3 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   6 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-3 aty)
%            Number of functors    :    8 (   8 usr;   8 con; 0-0 aty)
%            Number of variables   :   11 (  11   !;   0   ?)
% SPC      : 

% Comments : Requires CSR001+0.ax
%------------------------------------------------------------------------------
fof(initiates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( initiates(Event,Fluent,Time)
    <=> ( ( Event = push
          & Fluent = forwards
          & ~ happens(pull,Time) )
        | ( Event = pull
          & Fluent = backwards
          & ~ happens(push,Time) )
        | ( Event = pull
          & Fluent = spinning
          & happens(push,Time) ) ) ) ).

fof(terminates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( terminates(Event,Fluent,Time)
    <=> ( ( Event = push
          & Fluent = backwards
          & ~ happens(pull,Time) )
        | ( Event = pull
          & Fluent = forwards
          & ~ happens(push,Time) )
        | ( Event = pull
          & Fluent = forwards
          & happens(push,Time) )
        | ( Event = pull
          & Fluent = backwards
          & happens(push,Time) )
        | ( Event = push
          & Fluent = spinning
          & ~ happens(pull,Time) )
        | ( Event = pull
          & Fluent = spinning
          & ~ happens(push,Time) ) ) ) ).

fof(releases_all_defn,axiom,
    ! [Event,Fluent,Time] : ~ releases(Event,Fluent,Time) ).

fof(happens_all_defn,axiom,
    ! [Event,Time] :
      ( happens(Event,Time)
    <=> ( ( Event = push
          & Time = n0 )
        | ( Event = pull
          & Time = n1 )
        | ( Event = pull
          & Time = n2 )
        | ( Event = push
          & Time = n2 ) ) ) ).

%----Distinct events
fof(push_not_pull,axiom,
    push != pull ).

%----Distinct fluents
fof(forwards_not_backwards,axiom,
    forwards != backwards ).

fof(forwards_not_spinning,axiom,
    forwards != spinning ).

fof(spinning_not_backwards,axiom,
    spinning != backwards ).

%------------------------------------------------------------------------------

```

### ./CSR001+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : CSR001+3 : TPTP v8.2.0. Released .0.
% Domain   : Commonsense Reasoning
% Axioms   : Supermarket trolley scenario for multiple trolleys
% Version  : [Mue05] axioms : Especial.
% English  :

% Refs     : [Mue05] Mueller (2005), Email to Geoff Sutcliffe
% Source   : [Mue05]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    9 (   5 unt;   0 def)
%            Number of atoms       :   40 (  28 equ)
%            Maximal formula atoms :   19 (   4 avg)
%            Number of connectives :   48 (  17   ~;   7   |;  20   &)
%                                         (   2 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   15 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-3 aty)
%            Number of functors    :    5 (   5 usr;   0 con; 1-2 aty)
%            Number of variables   :   26 (  22   !;   4   ?)
% SPC      : 

% Comments : Requires CSR001+0.ax
%------------------------------------------------------------------------------
fof(initiates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( initiates(Event,Fluent,Time)
    <=> ? [Agent,Trolley] :
          ( ( Event = push(Agent,Trolley)
            & Fluent = forwards(Trolley)
            & ~ happens(pull(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = backwards(Trolley)
            & ~ happens(push(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = spinning(Trolley)
            & happens(push(Agent,Trolley),Time) ) ) ) ).

fof(terminates_all_defn,axiom,
    ! [Event,Fluent,Time] :
      ( terminates(Event,Fluent,Time)
    <=> ? [Agent,Trolley] :
          ( ( Event = push(Agent,Trolley)
            & Fluent = backwards(Trolley)
            & ~ happens(pull(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = forwards(Trolley)
            & ~ happens(push(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = forwards(Trolley)
            & happens(push(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = backwards(Trolley)
            & happens(push(Agent,Trolley),Time) )
          | ( Event = push(Agent,Trolley)
            & Fluent = spinning(Trolley)
            & ~ happens(pull(Agent,Trolley),Time) )
          | ( Event = pull(Agent,Trolley)
            & Fluent = spinning(Trolley)
            & ~ happens(push(Agent,Trolley),Time) ) ) ) ).

fof(releases_all_defn,axiom,
    ! [Event,Fluent,Time] : ~ releases(Event,Fluent,Time) ).

%----Distinct events
fof(push_not_pull,axiom,
    ! [Agent,Trolley] : push(Agent,Trolley) != pull(Agent,Trolley) ).

fof(push_unique,axiom,
    ! [Agent1,Agent2,Trolley1,Trolley2] :
      ( ( Agent1 != Agent2
        & Trolley1 != Trolley2 )
     => push(Agent1,Trolley1) != push(Agent2,Trolley2) ) ).

fof(pull_unique,axiom,
    ! [Agent1,Agent2,Trolley1,Trolley2] :
      ( ( Agent1 != Agent2
        & Trolley1 != Trolley2 )
     => pull(Agent1,Trolley1) != pull(Agent2,Trolley2) ) ).

%----Distinct fluents
fof(forwards_not_backwards,axiom,
    ! [Trolley] : forwards(Trolley) != backwards(Trolley) ).

fof(forwards_not_spinning,axiom,
    ! [Trolley] : forwards(Trolley) != spinning(Trolley) ).

fof(spinning_not_backwards,axiom,
    ! [Trolley] : spinning(Trolley) != backwards(Trolley) ).

%------------------------------------------------------------------------------

```

### ./CSR002+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : CSR002+0 : TPTP v8.2.0. Released v3.4.0.
% Domain   : Common Sense Reasoning
% Axioms   : 0 axioms from Cyc
% Version  : Especial.
% English  :

% Refs     : [RS+]   Reagan Smith et al., The Cyc TPTP Challenge Problem
% Source   : [RS+]
% Names    :

% Status   : Satisfiable
% Syntax   : WARNING: No formulae parsed from -t
% SPC      : 

% Comments : Autogenerated from the OpenCyc KB. Documentation can be found at
%            http://opencyc.org/doc/#TPTP_Challenge_Problem_Set
%          : Cyc(R) Knowledge Base Copyright(C) 1995-2007 Cycorp, Inc., Austin,
%            TX, USA. All rights reserved.
%          : OpenCyc Knowledge Base Copyright(C) 2001-2007 Cycorp, Inc.,
%            Austin, TX, USA. All rights reserved.
%------------------------------------------------------------------------------
%------------------------------------------------------------------------------

```

### ./CSR002+1.ax

Very long 5582

### ./CSR002+2.ax

Very long 38068

### ./CSR002+3.ax

Very long 203713

### ./CSR002+4.ax

Very long 2632820

### ./CSR002+5.ax

Very long 15512609

### ./CSR003+0.ax

Very long 36727

### ./CSR003+1.ax

Very long 80335

### ./CSR003+2.ax

Very long 287360

### ./CSR003+3.ax

Very long 22749

### ./CSR003+4.ax

Very long 63738

### ./CSR003+5.ax

Very long 268584

### ./CSR004+0.ax

Very long 31277

### ./CSR005^0.ax

Very long 20418

### ./CSR006+0.ax

Very long 35192

## Data Structures

### ./DAT001_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT001_0 : TPTP v8.2.0. Released v5.0.0.
% Domain   : Data Structures
% Axioms   : Integer arrays
% Version  : [Wal10] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   1 unt;   3 typ;   0 def)
%            Number of atoms       :    3 (   3 equ)
%            Maximal formula atoms :    2 (   0 avg)
%            Number of connectives :    1 (   0   ~;   1   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number arithmetic     :    5 (   0 atm;   0 fun;   0 num;   5 var)
%            Number of types       :    2 (   1 usr;   1 ari)
%            Number of type conns  :    5 (   2   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-3 aty)
%            Number of variables   :    7 (   7   !;   0   ?;   7   :)
% SPC      : TFF_SAT_RFO_SEQ_SAR

% Comments : 
%------------------------------------------------------------------------------
tff(array_type,type,
    array: $tType ).

tff(read_type,type,
    read: ( array * $int ) > $int ).

tff(write_type,type,
    write: ( array * $int * $int ) > array ).

tff(ax1,axiom,
    ! [U: array,V: $int,W: $int] : ( read(write(U,V,W),V) = W ) ).

tff(ax2,axiom,
    ! [X: array,Y: $int,Z: $int,X1: $int] :
      ( ( Y = Z )
      | ( read(write(X,Y,X1),Z) = read(X,Z) ) ) ).

%------------------------------------------------------------------------------

```

### ./DAT002=1.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT002=1 : TPTP v8.2.0. Released v5.0.0.
% Domain   : Data Structures
% Axioms   : Integer collections with counting
% Version  : [Wal10] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   1 unt;   1 typ;   0 def)
%            Number of atoms       :   20 (   7 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    8 (   2   ~;   0   |;   0   &)
%                                         (   5 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of FOOLs       :    7 (   7 fml;   0 var)
%            Number arithmetic     :   12 (   1 atm;   2 fun;   4 num;   5 var)
%            Number of types       :    1 (   0 usr;   1 ari)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    7 (   5 usr;   2 prp; 0-2 aty)
%            Number of functors    :    5 (   1 usr;   2 con; 0-2 aty)
%            Number of variables   :   12 (  12   !;   0   ?;  12   :)
% SPC      : TFF_SAT_RFO_SEQ_SAR

% Comments : Requires DAT002=0
%------------------------------------------------------------------------------
tff(count_type,type,
    count: collection > $int ).

tff(ax1,axiom,
    ! [X6: collection] : $greatereq(count(X6),0) ).

tff(ax2,axiom,
    ! [X7: collection] :
      ( ( X7 = empty )
    <=> ( count(X7) = 0 ) ) ).

tff(ax3,axiom,
    ! [X8: $int,X9: collection] :
      ( ~ in(X8,X9)
    <=> ( count(add(X8,X9)) = $sum(count(X9),1) ) ) ).

tff(ax4,axiom,
    ! [X10: $int,X11: collection] :
      ( in(X10,X11)
    <=> ( count(add(X10,X11)) = count(X11) ) ) ).

tff(ax5,axiom,
    ! [X12: $int,X13: collection] :
      ( in(X12,X13)
    <=> ( count(remove(X12,X13)) = $difference(count(X13),1) ) ) ).

tff(ax6,axiom,
    ! [X14: $int,X15: collection] :
      ( ~ in(X14,X15)
    <=> ( count(remove(X14,X15)) = count(X15) ) ) ).

tff(ax7,axiom,
    ! [X16: $int,X17: collection] :
      ( in(X16,X17)
     => ( X17 = add(X16,remove(X16,X17)) ) ) ).

%------------------------------------------------------------------------------

```

### ./DAT002_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT002_0 : TPTP v8.2.0. Released v5.0.0.
% Domain   : Data Structures
% Axioms   : Integer collections
% Version  : [Wal10] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :   10 (   3 unt;   5 typ;   0 def)
%            Number of atoms       :    9 (   2 equ)
%            Maximal formula atoms :    3 (   0 avg)
%            Number of connectives :    7 (   3   ~;   1   |;   1   &)
%                                         (   2 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number arithmetic     :    7 (   0 atm;   0 fun;   0 num;   7 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    6 (   3   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :   11 (  11   !;   0   ?;  11   :)
% SPC      : TFF_SAT_RFO_SEQ_SAR

% Comments : 
%------------------------------------------------------------------------------
tff(collection_type,type,
    collection: $tType ).

tff(empty_type,type,
    empty: collection ).

tff(add_type,type,
    add: ( $int * collection ) > collection ).

tff(remove_type,type,
    remove: ( $int * collection ) > collection ).

tff(in_type,type,
    in: ( $int * collection ) > $o ).

tff(ax1,axiom,
    ! [U: $int] : ~ in(U,empty) ).

tff(ax2,axiom,
    ! [V: $int,W: collection] : in(V,add(V,W)) ).

tff(ax3,axiom,
    ! [X: $int,Y: collection] : ~ in(X,remove(X,Y)) ).

tff(ax4,axiom,
    ! [Z: $int,X1: collection,X2: $int] :
      ( ( in(Z,X1)
        | ( Z = X2 ) )
    <=> in(Z,add(X2,X1)) ) ).

tff(ax5,axiom,
    ! [X3: $int,X4: collection,X5: $int] :
      ( ( in(X3,X4)
        & ( X3 != X5 ) )
    <=> in(X3,remove(X5,X4)) ) ).

%------------------------------------------------------------------------------

```

### ./DAT003_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT003_0 : TPTP v8.2.0. Released v5.0.0.
% Domain   : Data Structures
% Axioms   : Pointer data types
% Version  : [Wal10] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :   20 (   0 unt;   7 typ;   0 def)
%            Number of atoms       :   31 (   6 equ)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   27 (   9   ~;   0   |;   5   &)
%                                         (   0 <=>;  13  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   4 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number arithmetic     :    5 (   1 atm;   1 fun;   3 num;   0 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    6 (   6   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    3 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :    8 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   13 (  13   !;   0   ?;  13   :)
% SPC      : TFF_SAT_RFO_SEQ_SAR

% Comments : 
%------------------------------------------------------------------------------
tff(record_type,type,
    record: $tType ).

tff(length_type,type,
    length: record > $int ).

tff(next_type,type,
    next: record > record ).

tff(data_type,type,
    data: record > $int ).

tff(split1_type,type,
    split1: record > record ).

tff(split2_type,type,
    split2: record > record ).

tff(isrecord_type,type,
    isrecord: record > $o ).

tff(ax1,axiom,
    ! [U: record] :
      ( ~ isrecord(U)
     => ( length(U) = 0 ) ) ).

tff(ax2,axiom,
    ! [U: record] :
      ( isrecord(U)
     => $greatereq(length(U),1) ) ).

tff(ax3,axiom,
    ! [U: record] :
      ( isrecord(U)
     => ( length(U) = $sum(length(next(U)),1) ) ) ).

tff(ax4,axiom,
    ! [U: record] :
      ( ~ isrecord(U)
     => ~ isrecord(split1(U)) ) ).

tff(ax5,axiom,
    ! [U: record] :
      ( isrecord(U)
     => isrecord(split1(U)) ) ).

tff(ax6,axiom,
    ! [U: record] :
      ( isrecord(U)
     => ( data(split1(U)) = data(U) ) ) ).

tff(ax7,axiom,
    ! [U: record] :
      ( ( isrecord(U)
        & ~ isrecord(next(U)) )
     => ~ isrecord(next(split1(U))) ) ).

tff(ax8,axiom,
    ! [U: record] :
      ( ( isrecord(U)
        & isrecord(next(U)) )
     => ( next(split1(U)) = split1(next(next(U))) ) ) ).

tff(ax9,axiom,
    ! [U: record] :
      ( ~ isrecord(U)
     => ~ isrecord(split2(U)) ) ).

tff(ax10,axiom,
    ! [U: record] :
      ( ~ isrecord(next(U))
     => ~ isrecord(split2(U)) ) ).

tff(ax11,axiom,
    ! [U: record] :
      ( ( isrecord(U)
        & isrecord(next(U)) )
     => isrecord(split2(U)) ) ).

tff(ax12,axiom,
    ! [U: record] :
      ( ( isrecord(U)
        & isrecord(next(U)) )
     => ( data(split2(U)) = data(next(U)) ) ) ).

tff(ax13,axiom,
    ! [U: record] :
      ( ( isrecord(U)
        & isrecord(next(U)) )
     => ( next(split2(U)) = split2(next(next(U))) ) ) ).

%------------------------------------------------------------------------------

```

### ./DAT004_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT004_0 : TPTP v8.2.0. Released v5.5.0.
% Domain   : Data Structures
% Axioms   : Array data types
% Version  : [KIV] axioms.
% English  :

% Refs     : [Rei99] Reif (1999), Email to Geoff Sutcliffe
% Source   : [Rei99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   11 (   3 unt;   6 typ;   0 def)
%            Number of atoms       :    7 (   7 equ)
%            Maximal formula atoms :    2 (   0 avg)
%            Number of connectives :    3 (   1   ~;   0   |;   0   &)
%                                         (   1 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number arithmetic     :    6 (   0 atm;   0 fun;   0 num;   6 var)
%            Number of types       :    3 (   2 usr;   1 ari)
%            Number of type conns  :    5 (   2   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-3 aty)
%            Number of variables   :   15 (  15   !;   0   ?;  15   :)
% SPC      : TFF_SAT_EQU_ARI

% Comments : From: /home/magenta/KIV/newtppl/case-studies/hashtable/
%            specifications/array/
%------------------------------------------------------------------------------
tff(data_type,type,
    data: $tType ).

tff(array_type,type,
    array: $tType ).

tff(mkarray_type,type,
    mkarray: array ).

tff(none_type,type,
    none: data ).

tff(put_type,type,
    put: ( array * $int * data ) > array ).

tff(get_type,type,
    get: ( array * $int ) > data ).

tff(ax_17,axiom,
    ! [M: $int] : ( get(mkarray,M) = none ) ).

tff(ax_18,axiom,
    ! [Ar: array,M: $int,D: data] : ( get(put(Ar,M,D),M) = D ) ).

tff(ax_19,axiom,
    ! [N: $int,D: data,Ar: array,M: $int] :
      ( ( M != N )
     => ( get(put(Ar,N,D),M) = get(Ar,M) ) ) ).

tff(ax_20,axiom,
    ! [D2: data,Ar: array,M: $int,D1: data] : ( put(put(Ar,M,D2),M,D1) = put(Ar,M,D1) ) ).

tff(ax_21,axiom,
    ! [Ar: array,Ar0: array] :
      ( ( Ar = Ar0 )
    <=> ! [N: $int] : ( get(Ar,N) = get(Ar0,N) ) ) ).

%------------------------------------------------------------------------------

```

### ./DAT005_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT005_0 : TPTP v8.2.0. Released v5.5.0.
% Domain   : Data Structures
% Axioms   : Heap data types
% Version  : [KIV] axioms.
% English  :

% Refs     : [Rei99] Reif (1999), Email to Geoff Sutcliffe
% Source   : [Rei99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   18 (   7 unt;   7 typ;   0 def)
%            Number of atoms       :   18 (  11 equ)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   10 (   3   ~;   2   |;   2   &)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number arithmetic     :   10 (   0 atm;   1 fun;   2 num;   7 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    7 (   5   >;   2   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :   21 (  21   !;   0   ?;  21   :)
% SPC      : TFF_SAT_EQU_ARI

% Comments : 
%------------------------------------------------------------------------------
tff(heap_type,type,
    heap: $tType ).

tff(empty_type,type,
    empty: heap ).

tff(get_type,type,
    get: heap > heap ).

tff(app_type,type,
    app: ( heap * $int ) > heap ).

tff(toop_type,type,
    toop: heap > $int ).

tff(length_type,type,
    length: heap > $int ).

tff(lsls_type,type,
    lsls: ( heap * heap ) > $o ).

tff(ax_17,axiom,
    ! [N: $int,H: heap] : ( get(app(H,N)) = H ) ).

tff(ax_18,axiom,
    ! [H: heap,N: $int] : ( toop(app(H,N)) = N ) ).

tff(ax_19,axiom,
    ! [H: heap,H0: heap,N: $int,N0: $int] :
      ( ( app(H,N) = app(H0,N0) )
    <=> ( ( H = H0 )
        & ( N = N0 ) ) ) ).

tff(ax_20,axiom,
    ! [H: heap,N: $int] : ( empty != app(H,N) ) ).

tff(ax_21,axiom,
    ! [H: heap] :
      ( ( H = empty )
      | ( H = app(get(H),toop(H)) ) ) ).

tff(ax_22,axiom,
    length(empty) = 0 ).

tff(ax_23,axiom,
    ! [N: $int,H: heap] : ( length(app(H,N)) = $sum(1,length(H)) ) ).

tff(ax_24,axiom,
    ! [H: heap] : ~ lsls(H,H) ).

tff(ax_25,axiom,
    ! [H0: heap,H: heap,H1: heap] :
      ( ( lsls(H,H0)
        & lsls(H0,H1) )
     => lsls(H,H1) ) ).

tff(ax_26,axiom,
    ! [H: heap] : ~ lsls(H,empty) ).

tff(ax_27,axiom,
    ! [N: $int,H0: heap,H: heap] :
      ( lsls(H0,app(H,N))
    <=> ( ( H0 = H )
        | lsls(H0,H) ) ) ).

%------------------------------------------------------------------------------

```

### ./DAT006_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : DAT006_0 : TPTP v8.2.0. Released v5.5.0.
% Domain   : Data Structures
% Axioms   : Tree-heap data types
% Version  : [KIV] axioms.
% English  :

% Refs     : [Rei99] Reif (1999), Email to Geoff Sutcliffe
% Source   : [Rei99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   22 (   8 unt;   8 typ;   0 def)
%            Number of atoms       :   23 (  16 equ)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   13 (   4   ~;   2   |;   2   &)
%                                         (   2 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number arithmetic     :   20 (   0 atm;   3 fun;   5 num;  12 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :    9 (   6   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    9 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :   28 (  28   !;   0   ?;  28   :)
% SPC      : TFF_SAT_EQU_ARI

% Comments : From: /home/magenta/KIV/newtppl/case-studies/tree-heap/
%            specifications/sel/
%------------------------------------------------------------------------------
tff(heap_type,type,
    heap: $tType ).

tff(empty_type,type,
    empty: heap ).

tff(toop_type,type,
    toop: heap > $int ).

tff(sel_type,type,
    sel: ( heap * $int ) > $int ).

tff(length_type,type,
    length: heap > $int ).

tff(app_type,type,
    app: ( heap * $int ) > heap ).

tff(get_type,type,
    get: heap > heap ).

tff(lsls_type,type,
    lsls: ( heap * heap ) > $o ).

tff(ax_1,axiom,
    ! [M: $int] : ( sel(empty,M) = 0 ) ).

tff(ax_2,axiom,
    ! [H: heap,M: $int,N: $int] :
      ( ( M = $sum(1,length(H)) )
     => ( sel(app(H,N),M) = N ) ) ).

tff(ax_3,axiom,
    ! [N: $int,H: heap,M: $int] :
      ( ( M != $sum(1,length(H)) )
     => ( sel(app(H,N),M) = sel(H,M) ) ) ).

tff(ax_20,axiom,
    ! [N: $int,H: heap] : ( get(app(H,N)) = H ) ).

tff(ax_21,axiom,
    ! [H: heap,N: $int] : ( toop(app(H,N)) = N ) ).

tff(ax_22,axiom,
    ! [H: heap,H0: heap,N: $int,N0: $int] :
      ( ( app(H,N) = app(H0,N0) )
    <=> ( ( H = H0 )
        & ( N = N0 ) ) ) ).

tff(ax_23,axiom,
    ! [H: heap,N: $int] : ( empty != app(H,N) ) ).

tff(ax_24,axiom,
    ! [H: heap] :
      ( ( H = empty )
      | ( H = app(get(H),toop(H)) ) ) ).

tff(ax_25,axiom,
    length(empty) = 0 ).

tff(ax_26,axiom,
    ! [N: $int,H: heap] : ( length(app(H,N)) = $sum(1,length(H)) ) ).

tff(ax_27,axiom,
    ! [H: heap] : ~ lsls(H,H) ).

tff(ax_28,axiom,
    ! [H0: heap,H: heap,H1: heap] :
      ( ( lsls(H,H0)
        & lsls(H0,H1) )
     => lsls(H,H1) ) ).

tff(ax_29,axiom,
    ! [H: heap] : ~ lsls(H,empty) ).

tff(ax_30,axiom,
    ! [N: $int,H0: heap,H: heap] :
      ( lsls(H0,app(H,N))
    <=> ( ( H0 = H )
        | lsls(H0,H) ) ) ).

%------------------------------------------------------------------------------

```

## Field Theory

### ./FLD001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : FLD001-0 : TPTP v8.2.0. Released .0.
% Domain   : Field Theory (Ordered fields)
% Axioms   : Ordered field axioms (axiom formulation glxx)
% Version  : [Dra93] axioms : Especial.
% English  :

% Refs     : [Dra93] Draeger (1993), Anwendung des Theorembeweisers SETHEO
% Source   : [Dra93]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   27 (   3 unt;   3 nHn;  27 RR)
%            Number of literals    :   73 (   0 equ;  44 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-2 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-2 aty)
%            Number of variables   :   50 (   0 sgn)
% SPC      : 

% Comments : The missing equality axioms can be derived.
%          : Currently it is unknown if this axiomatization is complete.
%            It is definitely tuned for SETHEO.
% Bugfixes : .0 - Added different_identities clause.
%--------------------------------------------------------------------------
cnf(associativity_addition,axiom,
    ( equalish(add(X,add(Y,Z)),add(add(X,Y),Z))
    | ~ defined(X)
    | ~ defined(Y)
    | ~ defined(Z) ) ).

cnf(existence_of_identity_addition,axiom,
    ( equalish(add(additive_identity,X),X)
    | ~ defined(X) ) ).

cnf(existence_of_inverse_addition,axiom,
    ( equalish(add(X,additive_inverse(X)),additive_identity)
    | ~ defined(X) ) ).

cnf(commutativity_addition,axiom,
    ( equalish(add(X,Y),add(Y,X))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(associativity_multiplication,axiom,
    ( equalish(multiply(X,multiply(Y,Z)),multiply(multiply(X,Y),Z))
    | ~ defined(X)
    | ~ defined(Y)
    | ~ defined(Z) ) ).

cnf(existence_of_identity_multiplication,axiom,
    ( equalish(multiply(multiplicative_identity,X),X)
    | ~ defined(X) ) ).

cnf(existence_of_inverse_multiplication,axiom,
    ( equalish(multiply(X,multiplicative_inverse(X)),multiplicative_identity)
    | ~ defined(X)
    | equalish(X,additive_identity) ) ).

cnf(commutativity_multiplication,axiom,
    ( equalish(multiply(X,Y),multiply(Y,X))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(distributivity,axiom,
    ( equalish(add(multiply(X,Z),multiply(Y,Z)),multiply(add(X,Y),Z))
    | ~ defined(X)
    | ~ defined(Y)
    | ~ defined(Z) ) ).

cnf(well_definedness_of_addition,axiom,
    ( defined(add(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(well_definedness_of_additive_identity,axiom,
    defined(additive_identity) ).

cnf(well_definedness_of_additive_inverse,axiom,
    ( defined(additive_inverse(X))
    | ~ defined(X) ) ).

cnf(well_definedness_of_multiplication,axiom,
    ( defined(multiply(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(well_definedness_of_multiplicative_identity,axiom,
    defined(multiplicative_identity) ).

cnf(well_definedness_of_multiplicative_inverse,axiom,
    ( defined(multiplicative_inverse(X))
    | ~ defined(X)
    | equalish(X,additive_identity) ) ).

cnf(antisymmetry_of_order_relation,axiom,
    ( equalish(X,Y)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,X) ) ).

cnf(transitivity_of_order_relation,axiom,
    ( less_or_equal(X,Z)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,Z) ) ).

cnf(totality_of_order_relation,axiom,
    ( less_or_equal(X,Y)
    | less_or_equal(Y,X)
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(compatibility_of_order_relation_and_addition,axiom,
    ( less_or_equal(add(X,Z),add(Y,Z))
    | ~ defined(Z)
    | ~ less_or_equal(X,Y) ) ).

cnf(compatibility_of_order_relation_and_multiplication,axiom,
    ( less_or_equal(additive_identity,multiply(Y,Z))
    | ~ less_or_equal(additive_identity,Y)
    | ~ less_or_equal(additive_identity,Z) ) ).

cnf(reflexivity_of_equality,axiom,
    ( equalish(X,X)
    | ~ defined(X) ) ).

cnf(symmetry_of_equality,axiom,
    ( equalish(X,Y)
    | ~ equalish(Y,X) ) ).

cnf(transitivity_of_equality,axiom,
    ( equalish(X,Z)
    | ~ equalish(X,Y)
    | ~ equalish(Y,Z) ) ).

cnf(compatibility_of_equality_and_addition,axiom,
    ( equalish(add(X,Z),add(Y,Z))
    | ~ defined(Z)
    | ~ equalish(X,Y) ) ).

cnf(compatibility_of_equality_and_multiplication,axiom,
    ( equalish(multiply(X,Z),multiply(Y,Z))
    | ~ defined(Z)
    | ~ equalish(X,Y) ) ).

cnf(compatibility_of_equality_and_order_relation,axiom,
    ( less_or_equal(Y,Z)
    | ~ less_or_equal(X,Z)
    | ~ equalish(X,Y) ) ).

cnf(different_identities,axiom,
    ~ equalish(additive_identity,multiplicative_identity) ).

%--------------------------------------------------------------------------

```

### ./FLD002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : FLD002-0 : TPTP v8.2.0. Released .0.
% Domain   : Field Theory (Ordered fields)
% Axioms   : Ordered field axioms (axiom formulation re)
% Version  : [Dra93] axioms : Especial.
% English  :

% Refs     : [Dra93] Draeger (1993), Anwendung des Theorembeweisers SETHEO
% Source   : [Dra93]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   26 (   3 unt;   3 nHn;  26 RR)
%            Number of literals    :   77 (   0 equ;  49 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-2 aty)
%            Number of variables   :   73 (   0 sgn)
% SPC      : 

% Comments : The missing equality axioms can be derived.
%          : Currently it is unknown if this axiomatization is complete.
%            It is definitely tuned for SETHEO.
% Bugfixes : .0 - Added different_identities clause.
%--------------------------------------------------------------------------
cnf(associativity_addition_1,axiom,
    ( sum(X,V,W)
    | ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(U,Z,W) ) ).

cnf(associativity_addition_2,axiom,
    ( sum(U,Z,W)
    | ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(X,V,W) ) ).

cnf(existence_of_identity_addition,axiom,
    ( sum(additive_identity,X,X)
    | ~ defined(X) ) ).

cnf(existence_of_inverse_addition,axiom,
    ( sum(additive_inverse(X),X,additive_identity)
    | ~ defined(X) ) ).

cnf(commutativity_addition,axiom,
    ( sum(Y,X,Z)
    | ~ sum(X,Y,Z) ) ).

cnf(associativity_multiplication_1,axiom,
    ( product(X,V,W)
    | ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W) ) ).

cnf(associativity_multiplication_2,axiom,
    ( product(U,Z,W)
    | ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W) ) ).

cnf(existence_of_identity_multiplication,axiom,
    ( product(multiplicative_identity,X,X)
    | ~ defined(X) ) ).

cnf(existence_of_inverse_multiplication,axiom,
    ( product(multiplicative_inverse(X),X,multiplicative_identity)
    | sum(additive_identity,X,additive_identity)
    | ~ defined(X) ) ).

cnf(commutativity_multiplication,axiom,
    ( product(Y,X,Z)
    | ~ product(X,Y,Z) ) ).

cnf(distributivity_1,axiom,
    ( sum(C,D,B)
    | ~ sum(X,Y,A)
    | ~ product(A,Z,B)
    | ~ product(X,Z,C)
    | ~ product(Y,Z,D) ) ).

cnf(distributivity_2,axiom,
    ( product(A,Z,B)
    | ~ sum(X,Y,A)
    | ~ product(X,Z,C)
    | ~ product(Y,Z,D)
    | ~ sum(C,D,B) ) ).

cnf(well_definedness_of_addition,axiom,
    ( defined(add(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(well_definedness_of_additive_identity,axiom,
    defined(additive_identity) ).

cnf(well_definedness_of_additive_inverse,axiom,
    ( defined(additive_inverse(X))
    | ~ defined(X) ) ).

cnf(well_definedness_of_multiplication,axiom,
    ( defined(multiply(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(well_definedness_of_multiplicative_identity,axiom,
    defined(multiplicative_identity) ).

cnf(well_definedness_of_multiplicative_inverse,axiom,
    ( defined(multiplicative_inverse(X))
    | ~ defined(X)
    | sum(additive_identity,X,additive_identity) ) ).

cnf(totality_of_addition,axiom,
    ( sum(X,Y,add(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(totality_of_multiplication,axiom,
    ( product(X,Y,multiply(X,Y))
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(antisymmetry_of_order_relation,axiom,
    ( sum(additive_identity,X,Y)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,X) ) ).

cnf(transitivity_of_order_relation,axiom,
    ( less_or_equal(X,Z)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,Z) ) ).

cnf(totality_of_order_relation,axiom,
    ( less_or_equal(X,Y)
    | less_or_equal(Y,X)
    | ~ defined(X)
    | ~ defined(Y) ) ).

cnf(compatibility_of_order_relation_and_addition,axiom,
    ( less_or_equal(U,V)
    | ~ less_or_equal(X,Y)
    | ~ sum(X,Z,U)
    | ~ sum(Y,Z,V) ) ).

cnf(compatibility_of_order_relation_and_multiplication,axiom,
    ( less_or_equal(additive_identity,Z)
    | ~ less_or_equal(additive_identity,X)
    | ~ less_or_equal(additive_identity,Y)
    | ~ product(X,Y,Z) ) ).

cnf(different_identities,axiom,
    ~ sum(additive_identity,additive_identity,multiplicative_identity) ).

%--------------------------------------------------------------------------

```

## Geometry

### ./GEO001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO001-0 : TPTP v8.2.0. Bugfixed v2.5.0
% Domain   : Geometry (Tarskian)
% Axioms   : Tarski geometry axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   20 (   6 unt;   6 nHn;  17 RR)
%            Number of literals    :   64 (   8 equ;  38 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-4 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-6 aty)
%            Number of variables   :   79 (   3 sgn)
% SPC      : 

% Comments : These axioms are also used in [Wos88], p.206.
%          : outer_pasch : Skolem function arising from Outer Pasch Axiom (A7)
%            euclid1 : Skolem function arising from Euclid's Axiom (A8)
%            euclid2 : Skolem function arising from Euclid's Axiom (A8)
%            extend : Skolem function from Segment Construction (A10)
%            cont : Skolem function from Weakened Elementary Continuity (A13')
% Bugfixes : v2.5.0 - Fixed clause continuity1.
%--------------------------------------------------------------------------
cnf(identity_for_betweeness,axiom,
    ( ~ between(X,Y,X)
    | X = Y ) ).

cnf(transitivity_for_betweeness,axiom,
    ( ~ between(X,Y,V)
    | ~ between(Y,Z,V)
    | between(X,Y,Z) ) ).

cnf(connectivity_for_betweeness,axiom,
    ( ~ between(X,Y,Z)
    | ~ between(X,Y,V)
    | X = Y
    | between(X,Z,V)
    | between(X,V,Z) ) ).

cnf(reflexivity_for_equidistance,axiom,
    equidistant(X,Y,Y,X) ).

cnf(identity_for_equidistance,axiom,
    ( ~ equidistant(X,Y,Z,Z)
    | X = Y ) ).

cnf(transitivity_for_equidistance,axiom,
    ( ~ equidistant(X,Y,Z,V)
    | ~ equidistant(X,Y,V2,W)
    | equidistant(Z,V,V2,W) ) ).

cnf(outer_pasch1,axiom,
    ( ~ between(X,W,V)
    | ~ between(Y,V,Z)
    | between(X,outer_pasch(W,X,Y,Z,V),Y) ) ).

cnf(outer_pasch2,axiom,
    ( ~ between(X,W,V)
    | ~ between(Y,V,Z)
    | between(Z,W,outer_pasch(W,X,Y,Z,V)) ) ).

cnf(euclid1,axiom,
    ( ~ between(X,V,W)
    | ~ between(Y,V,Z)
    | X = V
    | between(X,Z,euclid1(W,X,Y,Z,V)) ) ).

cnf(euclid2,axiom,
    ( ~ between(X,V,W)
    | ~ between(Y,V,Z)
    | X = V
    | between(X,Y,euclid2(W,X,Y,Z,V)) ) ).

cnf(euclid3,axiom,
    ( ~ between(X,V,W)
    | ~ between(Y,V,Z)
    | X = V
    | between(euclid1(W,X,Y,Z,V),W,euclid2(W,X,Y,Z,V)) ) ).

cnf(outer_five_segment,axiom,
    ( ~ equidistant(X,Y,X1,Y1)
    | ~ equidistant(Y,Z,Y1,Z1)
    | ~ equidistant(X,V,X1,V1)
    | ~ equidistant(Y,V,Y1,V1)
    | ~ between(X,Y,Z)
    | ~ between(X1,Y1,Z1)
    | X = Y
    | equidistant(Z,V,Z1,V1) ) ).

cnf(segment_construction1,axiom,
    between(X,Y,extension(X,Y,W,V)) ).

cnf(segment_construction2,axiom,
    equidistant(Y,extension(X,Y,W,V),W,V) ).

cnf(lower_dimension1,axiom,
    ~ between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3) ).

cnf(lower_dimension2,axiom,
    ~ between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1) ).

cnf(lower_dimension3,axiom,
    ~ between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2) ).

cnf(upper_dimension,axiom,
    ( ~ equidistant(X,W,X,V)
    | ~ equidistant(Y,W,Y,V)
    | ~ equidistant(Z,W,Z,V)
    | between(X,Y,Z)
    | between(Y,Z,X)
    | between(Z,X,Y)
    | W = V ) ).

cnf(continuity1,axiom,
    ( ~ equidistant(V,X,V,X1)
    | ~ equidistant(V,Z,V,Z1)
    | ~ between(V,X,Z)
    | ~ between(X,Y,Z)
    | equidistant(V,Y,V,continuous(X,Y,Z,X1,Z1,V)) ) ).

cnf(continuity2,axiom,
    ( ~ equidistant(V,X,V,X1)
    | ~ equidistant(V,Z,V,Z1)
    | ~ between(V,X,Z)
    | ~ between(X,Y,Z)
    | between(X1,continuous(X,Y,Z,X1,Z1,V),Z1) ) ).

%--------------------------------------------------------------------------

```

### ./GEO001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Tarskian)
% Axioms   : Colinearity axioms for the GEO001 geometry axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   0 unt;   1 nHn;   4 RR)
%            Number of literals    :   10 (   0 equ;   4 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   12 (   0 sgn)
% SPC      : 

% Comments : Requires GEO001-0.ax
%--------------------------------------------------------------------------
cnf(colinearity1,axiom,
    ( ~ colinear(X,Y,Z)
    | between(X,Y,Z)
    | between(Y,X,Z)
    | between(X,Z,Y) ) ).

cnf(colinearity2,axiom,
    ( ~ between(X,Y,Z)
    | colinear(X,Y,Z) ) ).

cnf(colinearity3,axiom,
    ( ~ between(Y,X,Z)
    | colinear(X,Y,Z) ) ).

cnf(colinearity4,axiom,
    ( ~ between(X,Z,Y)
    | colinear(X,Y,Z) ) ).

%--------------------------------------------------------------------------

```

### ./GEO002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Tarskian)
% Axioms   : Tarski geometry axioms
% Version  : [Qua89] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Qua89] Quaife (1989), Automated Development of Tarski's Geome
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   18 (   6 unt;   5 nHn;  15 RR)
%            Number of literals    :   56 (   7 equ;  34 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-4 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-6 aty)
%            Number of variables   :   71 (   3 sgn)
% SPC      : 

% Comments : See [Qua89] p.100, for details of the differences from the
%            [MOW76] axioms.
%          : Skolem functions are:
%                inner_pasch : From Inner Pasch Axiom (A7)
%                euclid1     : From Euclid's Axiom (A8)
%                euclid2     : From Euclid's Axiom (A8)
%                extend      : From the Segment Construction Axiom (A10)
%                continuous  : From the Weakened form of the Elementary
%                              Continuity Axiom (A13')
%--------------------------------------------------------------------------
%----A1 - Reflexivity axiom for equidistance
cnf(reflexivity_for_equidistance,axiom,
    equidistant(X,Y,Y,X) ).

%----A2 - Transitivity axiom for equidistance
cnf(transitivity_for_equidistance,axiom,
    ( ~ equidistant(X,Y,Z,V)
    | ~ equidistant(X,Y,V2,W)
    | equidistant(Z,V,V2,W) ) ).

%----A3 Indentity axiom for equidistance
cnf(identity_for_equidistance,axiom,
    ( ~ equidistant(X,Y,Z,Z)
    | X = Y ) ).

%----A4 - Segment construction axiom, two clauses.
%----A4.1
cnf(segment_construction1,axiom,
    between(X,Y,extension(X,Y,W,V)) ).

%----A4.2
cnf(segment_construction2,axiom,
    equidistant(Y,extension(X,Y,W,V),W,V) ).

%----A5 - Outer five-segment axiom
cnf(outer_five_segment,axiom,
    ( ~ equidistant(X,Y,X1,Y1)
    | ~ equidistant(Y,Z,Y1,Z1)
    | ~ equidistant(X,V,X1,V1)
    | ~ equidistant(Y,V,Y1,V1)
    | ~ between(X,Y,Z)
    | ~ between(X1,Y1,Z1)
    | X = Y
    | equidistant(Z,V,Z1,V1) ) ).

%----A6 - Identity axiom for betweenness
cnf(identity_for_betweeness,axiom,
    ( ~ between(X,Y,X)
    | X = Y ) ).

%----A7 - Inner Pasch axiom, two clauses.
%----A7.1
cnf(inner_pasch1,axiom,
    ( ~ between(U,V,W)
    | ~ between(Y,X,W)
    | between(V,inner_pasch(U,V,W,X,Y),Y) ) ).

%----A7.2
cnf(inner_pasch2,axiom,
    ( ~ between(U,V,W)
    | ~ between(Y,X,W)
    | between(X,inner_pasch(U,V,W,X,Y),U) ) ).

%----A8 - Lower dimension axiom, three clauses.
%----A8.1
cnf(lower_dimension1,axiom,
    ~ between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3) ).

%----A8.2
cnf(lower_dimension2,axiom,
    ~ between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1) ).

%----A8.3
cnf(lower_dimension3,axiom,
    ~ between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2) ).

%----A9 - Upper dimension axiom
cnf(upper_dimension,axiom,
    ( ~ equidistant(X,W,X,V)
    | ~ equidistant(Y,W,Y,V)
    | ~ equidistant(Z,W,Z,V)
    | between(X,Y,Z)
    | between(Y,Z,X)
    | between(Z,X,Y)
    | W = V ) ).

%----A10 - Euclid's axiom, three clauses.
%----A10.1
cnf(euclid1,axiom,
    ( ~ between(U,W,Y)
    | ~ between(V,W,X)
    | U = W
    | between(U,V,euclid1(U,V,W,X,Y)) ) ).

%----A10.2
cnf(euclid2,axiom,
    ( ~ between(U,W,Y)
    | ~ between(V,W,X)
    | U = W
    | between(U,X,euclid2(U,V,W,X,Y)) ) ).

%----A10.3
cnf(euclid3,axiom,
    ( ~ between(U,W,Y)
    | ~ between(V,W,X)
    | U = W
    | between(euclid1(U,V,W,X,Y),Y,euclid2(U,V,W,X,Y)) ) ).

%----A11 - Weakened continuity axiom, two clauses.
%----A11.1
cnf(continuity1,axiom,
    ( ~ equidistant(U,V,U,V1)
    | ~ equidistant(U,X,U,X1)
    | ~ between(U,V,X)
    | ~ between(V,W,X)
    | between(V1,continuous(U,V,V1,W,X,X1),X1) ) ).

%----A11.2
cnf(continuity2,axiom,
    ( ~ equidistant(U,V,U,V1)
    | ~ equidistant(U,X,U,X1)
    | ~ between(U,V,X)
    | ~ between(V,W,X)
    | equidistant(U,W,U,continuous(U,V,V1,W,X,X1)) ) ).

%--------------------------------------------------------------------------

```

### ./GEO002-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO002-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Tarskian)
% Axioms   : Colinearity axioms for the GEO002 geometry axioms
% Version  : [Qua89] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Qua89] Quaife (1989), Automated Development of Tarski's Geome
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   0 unt;   1 nHn;   4 RR)
%            Number of literals    :   10 (   0 equ;   4 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   12 (   0 sgn)
% SPC      : 

% Comments : Requires GEO002-0.ax
%          : This version differs from the originals only in the ordering
%            of betweenness arguments. The equivalence is obvious from the
%            symmetry of betweenness.
%--------------------------------------------------------------------------
cnf(colinearity1,axiom,
    ( ~ between(X,Y,Z)
    | colinear(X,Y,Z) ) ).

cnf(colinearity2,axiom,
    ( ~ between(Y,Z,X)
    | colinear(X,Y,Z) ) ).

cnf(colinearity3,axiom,
    ( ~ between(Z,X,Y)
    | colinear(X,Y,Z) ) ).

cnf(colinearity4,axiom,
    ( ~ colinear(X,Y,Z)
    | between(X,Y,Z)
    | between(Y,Z,X)
    | between(Z,X,Y) ) ).

%--------------------------------------------------------------------------

```

### ./GEO002-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO002-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Tarskian)
% Axioms   : Reflection axioms for the GEO002 geometry axioms
% Version  : [Qua89] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Qua89] Quaife (1989), Automated Development of Tarski's Geome
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   1 unt;   0 nHn;   0 RR)
%            Number of literals    :    1 (   1 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-4 aty)
%            Number of variables   :    2 (   0 sgn)
% SPC      : 

% Comments : Requires GEO002-0.ax
%--------------------------------------------------------------------------
cnf(reflection,axiom,
    reflection(U,V) = extension(U,V,U,V) ).

%--------------------------------------------------------------------------

```

### ./GEO002-3.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO002-3 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Tarskian)
% Axioms   : Insertion axioms for the GEO002 geometry axioms
% Version  : [Qua89] axioms.
% English  :

% Refs     : [Tar59] Tarski (1959), What is Elementary Geometry?
%          : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Qua89] Quaife (1989), Automated Development of Tarski's Geome
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   1 unt;   0 nHn;   0 RR)
%            Number of literals    :    1 (   1 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-4 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : 

% Comments : Requires GEO002-0.ax
%--------------------------------------------------------------------------
cnf(insertion,axiom,
    insertion(U1,W1,U,V) = extension(extension(W1,U1,lower_dimension_point_1,lower_dimension_point_2),U1,U,V) ).

%--------------------------------------------------------------------------

```

### ./GEO003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Geometry (Hilbert)
% Axioms   : Hilbert geometry axioms
% Version  : [Ben92] axioms.
% English  :

% Refs     : [Ben92] Benana992), Recognising Unnecessary Clauses in Res
% Source   : [Ben92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   31 (   1 unt;  18 nHn;  31 RR)
%            Number of literals    :  174 (  43 equ; 103 neg)
%            Maximal clause size   :   16 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :   10 (  10 usr;   1 con; 0-3 aty)
%            Number of variables   :   70 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Axiom 1 : For any two distinct points, there is a unique line through
%----them.
cnf(axiom_G1A,axiom,
    ( on(Z1,line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1B,axiom,
    ( on(Z2,line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1C,axiom,
    ( line(line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1D,axiom,
    ( ~ on(Z1,Y3)
    | Z1 = Z2
    | ~ on(Z2,Y3)
    | Y3 = Y4
    | ~ on(Z1,Y4)
    | ~ on(Z2,Y4)
    | ~ point(Z1)
    | ~ point(Z2)
    | ~ line(Y3)
    | ~ line(Y4) ) ).

%----For any line, there are at least two points on the line.
cnf(axiom_G2A,axiom,
    ( on(point_1_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G2B,axiom,
    ( on(point_2_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G2C,axiom,
    ( point(point_1_on_line(Y1))
    | ~ line(Y1) ) ).

cnf(axiom_G2D,axiom,
    ( point(point_2_on_line(Y1))
    | ~ line(Y1) ) ).

cnf(axiom_G2E,axiom,
    ( point_1_on_line(Y1) != point_2_on_line(Y1)
    | ~ line(Y1) ) ).

%----For any line, there is a point not on the line.
cnf(axiom_G3A,axiom,
    ( ~ on(point_not_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G3B,axiom,
    ( point(point_not_on_line(Y1))
    | ~ line(Y1) ) ).

%----There exists at least one line
cnf(axiom_G4A,axiom,
    line(at_least_one_line) ).

%----For any plane there is a point on the plane.
cnf(axiom_G5A,axiom,
    ( ~ plane(Z1)
    | on(point_on_plane(Z1),Z1) ) ).

cnf(axiom_G5B,axiom,
    ( ~ plane(Z1)
    | point(point_on_plane(Z1)) ) ).

%----For any plane there is a point not on the plane.
cnf(axiom_G6A,axiom,
    ( ~ plane(Z1)
    | ~ on(point_not_on_plane(Z1),Z1) ) ).

cnf(axiom_G6B,axiom,
    ( ~ plane(Z1)
    | point(point_not_on_plane(Z1)) ) ).

%----For any three non-collinear points there is a unique plane through
%----them.
cnf(axiom_G7A,axiom,
    ( on(X1,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7B,axiom,
    ( on(X2,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7C,axiom,
    ( on(X3,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7D,axiom,
    ( plane(plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7E,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | ~ on(X1,Z1)
    | ~ on(X2,Z1)
    | ~ on(X3,Z1)
    | ~ plane(Z1)
    | ~ on(X1,Z2)
    | ~ on(X2,Z2)
    | ~ on(X3,Z2)
    | ~ plane(Z2)
    | Z1 = Z2 ) ).

%----If two points of a line are in the same plane then every point
%----of that line is in the plane.
cnf(axiom_G8A,axiom,
    ( ~ on(X1,Y1)
    | ~ on(X2,Y1)
    | ~ on(X1,Z1)
    | ~ on(X2,Z1)
    | ~ plane(Z1)
    | ~ point(X1)
    | ~ point(X2)
    | ~ line(Y1)
    | X1 = X2
    | on(Y1,Z1) ) ).

%----If two planes have a point in common they have at least one more
%----point in common.
cnf(axiom_G9A,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ on(X1,Z1)
    | ~ on(X1,Z2)
    | ~ point(X1)
    | on(common_point_on_planes(Z1,Z2,X1),Z1) ) ).

cnf(axiom_G9B,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ on(X1,Z1)
    | ~ on(X1,Z2)
    | ~ point(X1)
    | on(common_point_on_planes(Z1,Z2,X1),Z2) ) ).

cnf(axiom_G9C,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ on(X1,Z1)
    | ~ on(X1,Z2)
    | ~ point(X1)
    | point(common_point_on_planes(Z1,Z2,X1)) ) ).

cnf(axiom_G9D,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ on(X1,Z1)
    | ~ on(X1,Z2)
    | ~ point(X1)
    | X1 != common_point_on_planes(Z1,Z2,X1) ) ).

%----Three distinct points are collinear if and only if there is a line
%----through them.
cnf(axiom_G10A,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | on(X1,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10B,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | on(X2,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10C,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | on(X3,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10D,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | line(line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10E,axiom,
    ( collinear(X1,X2,X3)
    | ~ on(X1,Y)
    | ~ on(X2,Y)
    | ~ on(X3,Y)
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | ~ line(Y) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004+0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Simple curve axioms
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   16 (   1 unt;   0 def)
%            Number of atoms       :   67 (  10 equ)
%            Maximal formula atoms :   12 (   4 avg)
%            Number of connectives :   55 (   4   ~;   9   |;  21   &)
%                                         (   9 <=>;  12  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   53 (  44   !;   9   ?)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
fof(part_of_defn,axiom,
    ! [C,C1] :
      ( part_of(C1,C)
    <=> ! [P] :
          ( incident_c(P,C1)
         => incident_c(P,C) ) ) ).

fof(sum_defn,axiom,
    ! [C,C1,C2] :
      ( C = sum(C1,C2)
    <=> ! [Q] :
          ( incident_c(Q,C)
        <=> ( incident_c(Q,C1)
            | incident_c(Q,C2) ) ) ) ).

fof(end_point_defn,axiom,
    ! [P,C] :
      ( end_point(P,C)
    <=> ( incident_c(P,C)
        & ! [C1,C2] :
            ( ( part_of(C1,C)
              & part_of(C2,C)
              & incident_c(P,C1)
              & incident_c(P,C2) )
           => ( part_of(C1,C2)
              | part_of(C2,C1) ) ) ) ) ).

fof(inner_point_defn,axiom,
    ! [P,C] :
      ( inner_point(P,C)
    <=> ( incident_c(P,C)
        & ~ end_point(P,C) ) ) ).

fof(meet_defn,axiom,
    ! [P,C,C1] :
      ( meet(P,C,C1)
    <=> ( incident_c(P,C)
        & incident_c(P,C1)
        & ! [Q] :
            ( ( incident_c(Q,C)
              & incident_c(Q,C1) )
           => ( end_point(Q,C)
              & end_point(Q,C1) ) ) ) ) ).

fof(closed_defn,axiom,
    ! [C] :
      ( closed(C)
    <=> ~ ? [P] : end_point(P,C) ) ).

fof(open_defn,axiom,
    ! [C] :
      ( open(C)
    <=> ? [P] : end_point(P,C) ) ).

fof(c1,axiom,
    ! [C,C1] :
      ( ( part_of(C1,C)
        & C1 != C )
     => open(C1) ) ).

fof(c2,axiom,
    ! [C,C1,C2,C3] :
      ( ( part_of(C1,C)
        & part_of(C2,C)
        & part_of(C3,C)
        & ? [P] :
            ( end_point(P,C1)
            & end_point(P,C2)
            & end_point(P,C3) ) )
     => ( part_of(C2,C3)
        | part_of(C3,C2)
        | part_of(C1,C2)
        | part_of(C2,C1)
        | part_of(C1,C3)
        | part_of(C3,C1) ) ) ).

fof(c3,axiom,
    ! [C] :
    ? [P] : inner_point(P,C) ).

fof(c4,axiom,
    ! [C,P] :
      ( inner_point(P,C)
     => ? [C1,C2] :
          ( meet(P,C1,C2)
          & C = sum(C1,C2) ) ) ).

fof(c5,axiom,
    ! [C,P,Q,R] :
      ( ( end_point(P,C)
        & end_point(Q,C)
        & end_point(R,C) )
     => ( P = Q
        | P = R
        | Q = R ) ) ).

fof(c6,axiom,
    ! [C,P] :
      ( end_point(P,C)
     => ? [Q] :
          ( end_point(Q,C)
          & P != Q ) ) ).

fof(c7,axiom,
    ! [C,C1,C2,P] :
      ( ( closed(C)
        & meet(P,C1,C2)
        & C = sum(C1,C2) )
     => ! [Q] :
          ( end_point(Q,C1)
         => meet(Q,C1,C2) ) ) ).

fof(c8,axiom,
    ! [C1,C2] :
      ( ? [P] : meet(P,C1,C2)
     => ? [C] : C = sum(C1,C2) ) ).

fof(c9,axiom,
    ! [C,C1] :
      ( ! [P] :
          ( incident_c(P,C)
        <=> incident_c(P,C1) )
     => C = C1 ) ).

%--------------------------------------------------------------------------

```

### ./GEO004+1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004+1 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Betweenness for simple curves
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    1 (   0 unt;   0 def)
%            Number of atoms       :    6 (   1 equ)
%            Maximal formula atoms :    6 (   6 avg)
%            Number of connectives :    6 (   1   ~;   0   |;   4   &)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   11 (  11 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-4 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    5 (   4   !;   1   ?)
% SPC      : 

% Comments : Requires GEO004+0.ax
%--------------------------------------------------------------------------
fof(between_c_defn,axiom,
    ! [C,P,Q,R] :
      ( between_c(C,P,Q,R)
    <=> ( P != R
        & ? [Cpp] :
            ( part_of(Cpp,C)
            & end_point(P,Cpp)
            & end_point(R,Cpp)
            & inner_point(Q,Cpp) ) ) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004+2.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004+2 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Oriented curves
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   10 (   1 unt;   0 def)
%            Number of atoms       :   39 (   5 equ)
%            Maximal formula atoms :    7 (   3 avg)
%            Number of connectives :   32 (   3   ~;   1   |;  13   &)
%                                         (  10 <=>;   5  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    9 (   8 usr;   0 prp; 1-4 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :   36 (  32   !;   4   ?)
% SPC      : 

% Comments : Requires GEO004+0.ax GEO004+1.ax
%--------------------------------------------------------------------------
fof(between_o_defn,axiom,
    ! [O,P,Q,R] :
      ( between_o(O,P,Q,R)
    <=> ( ( ordered_by(O,P,Q)
          & ordered_by(O,Q,R) )
        | ( ordered_by(O,R,Q)
          & ordered_by(O,Q,P) ) ) ) ).

fof(start_point_defn,axiom,
    ! [P,O] :
      ( start_point(P,O)
    <=> ( incident_o(P,O)
        & ! [Q] :
            ( ( P != Q
              & incident_o(Q,O) )
           => ordered_by(O,P,Q) ) ) ) ).

fof(finish_point_defn,axiom,
    ! [P,O] :
      ( finish_point(P,O)
    <=> ( incident_o(P,O)
        & ! [Q] :
            ( ( P != Q
              & incident_o(Q,O) )
           => ordered_by(O,Q,P) ) ) ) ).

fof(o1,axiom,
    ! [O,P,Q] :
      ( ordered_by(O,P,Q)
     => ( incident_o(P,O)
        & incident_o(Q,O) ) ) ).

fof(o2,axiom,
    ! [O] :
    ? [C] :
      ( open(C)
      & ! [P] :
          ( incident_o(P,O)
        <=> incident_c(P,C) ) ) ).

fof(o3,axiom,
    ! [P,Q,R,O] :
      ( between_o(O,P,Q,R)
    <=> ? [C] :
          ( ! [P] :
              ( incident_o(P,O)
            <=> incident_c(P,C) )
          & between_c(C,P,Q,R) ) ) ).

fof(o4,axiom,
    ! [O] :
    ? [P] : start_point(P,O) ).

fof(o5,axiom,
    ! [P,Q,C] :
      ( ( open(C)
        & P != Q
        & incident_c(P,C)
        & incident_c(Q,C) )
     => ? [O] :
          ( ! [R] :
              ( incident_o(R,O)
            <=> incident_c(R,C) )
          & ordered_by(O,P,Q) ) ) ).

fof(o6,axiom,
    ! [O1,O2] :
      ( ! [P,Q] :
          ( ordered_by(O1,P,Q)
        <=> ordered_by(O2,P,Q) )
     => O1 = O2 ) ).

fof(underlying_curve_defn,axiom,
    ! [C,O] :
      ( C = underlying_curve(O)
    <=> ! [P] :
          ( incident_o(P,O)
        <=> incident_c(P,C) ) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004+3.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004+3 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Trajectories
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    9 (   1 unt;   0 def)
%            Number of atoms       :   20 (   1 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   12 (   1   ~;   0   |;   3   &)
%                                         (   4 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   24 (  22   !;   2   ?)
% SPC      : 

% Comments : Requires GEO004+0.ax GEO004+1.ax GEO004+2.ax
%--------------------------------------------------------------------------
fof(connect_defn,axiom,
    ! [X,Y,P] :
      ( connect(X,Y,P)
    <=> once(at_the_same_time(at(X,P),at(Y,P))) ) ).

fof(symmetry_of_at_the_same_time,axiom,
    ! [A,B] :
      ( once(at_the_same_time(A,B))
    <=> once(at_the_same_time(B,A)) ) ).

fof(assciativity_of_at_the_same_time,axiom,
    ! [A,B,C] :
      ( once(at_the_same_time(at_the_same_time(A,B),C))
    <=> once(at_the_same_time(A,at_the_same_time(B,C))) ) ).

fof(idempotence_of_at_the_same_time,axiom,
    ! [A] :
      ( once(A)
     => once(at_the_same_time(A,A)) ) ).

fof(conjunction_at_the_same_time,axiom,
    ! [A,B] :
      ( once(at_the_same_time(A,B))
     => ( once(A)
        & once(B) ) ) ).

fof(at_on_trajectory,axiom,
    ! [X,P] :
      ( once(at(X,P))
    <=> incident_o(P,trajectory_of(X)) ) ).

fof(trajectories_are_oriented_curves,axiom,
    ! [X] :
    ? [O] : trajectory_of(X) = O ).

fof(homogeneous_behaviour,axiom,
    ! [P1,P2,Q1,Q2,X,Y] :
      ( ( once(at_the_same_time(at(X,P1),at(Y,P2)))
        & once(at_the_same_time(at(X,Q1),at(Y,Q2))) )
     => ~ ( ordered_by(trajectory_of(X),P1,Q1)
          & ordered_by(trajectory_of(Y),Q2,P2) ) ) ).

fof(localization,axiom,
    ! [A] :
      ( once(A)
     => ! [X] :
        ? [P] : once(at_the_same_time(A,at(X,P))) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004-0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Simple curve axioms
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   48 (   1 unt;  21 nHn;  43 RR)
%            Number of literals    :  154 (  21 equ;  78 neg)
%            Maximal clause size   :   12 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :   14 (  14 usr;   0 con; 1-3 aty)
%            Number of variables   :  126 (  10 sgn)
% SPC      : 

% Comments : Created by tptp2X -f tptp -t clausify:otter GEO004+0.ax
%--------------------------------------------------------------------------
cnf(part_of_defn_1,axiom,
    ( ~ part_of(A,B)
    | ~ incident_c(C,A)
    | incident_c(C,B) ) ).

cnf(part_of_defn_2,axiom,
    ( incident_c(ax0_sk1(A,B),A)
    | part_of(A,B) ) ).

cnf(part_of_defn_3,axiom,
    ( ~ incident_c(ax0_sk1(A,B),B)
    | part_of(A,B) ) ).

cnf(sum_defn_4,axiom,
    ( A != sum(B,C)
    | ~ incident_c(D,A)
    | incident_c(D,B)
    | incident_c(D,C) ) ).

cnf(sum_defn_5,axiom,
    ( A != sum(B,C)
    | ~ incident_c(D,B)
    | incident_c(D,A) ) ).

cnf(sum_defn_6,axiom,
    ( A != sum(B,C)
    | ~ incident_c(D,C)
    | incident_c(D,A) ) ).

cnf(sum_defn_7,axiom,
    ( incident_c(ax0_sk2(A,B,C),C)
    | incident_c(ax0_sk2(A,B,C),B)
    | incident_c(ax0_sk2(A,B,C),A)
    | C = sum(B,A) ) ).

cnf(sum_defn_8,axiom,
    ( incident_c(ax0_sk2(A,B,C),C)
    | ~ incident_c(ax0_sk2(A,B,C),C)
    | C = sum(B,A) ) ).

cnf(sum_defn_9,axiom,
    ( ~ incident_c(ax0_sk2(A,B,C),B)
    | incident_c(ax0_sk2(A,B,C),B)
    | incident_c(ax0_sk2(A,B,C),A)
    | C = sum(B,A) ) ).

cnf(sum_defn_10,axiom,
    ( ~ incident_c(ax0_sk2(A,B,C),A)
    | incident_c(ax0_sk2(A,B,C),B)
    | incident_c(ax0_sk2(A,B,C),A)
    | C = sum(B,A) ) ).

cnf(sum_defn_11,axiom,
    ( ~ incident_c(ax0_sk2(A,B,C),B)
    | ~ incident_c(ax0_sk2(A,B,C),C)
    | C = sum(B,A) ) ).

cnf(sum_defn_12,axiom,
    ( ~ incident_c(ax0_sk2(A,B,C),A)
    | ~ incident_c(ax0_sk2(A,B,C),C)
    | C = sum(B,A) ) ).

cnf(end_point_defn_13,axiom,
    ( ~ end_point(A,B)
    | incident_c(A,B) ) ).

cnf(end_point_defn_14,axiom,
    ( ~ end_point(A,B)
    | ~ part_of(C,B)
    | ~ part_of(D,B)
    | ~ incident_c(A,C)
    | ~ incident_c(A,D)
    | part_of(C,D)
    | part_of(D,C) ) ).

cnf(end_point_defn_15,axiom,
    ( ~ incident_c(A,B)
    | part_of(ax0_sk3(B,A),B)
    | end_point(A,B) ) ).

cnf(end_point_defn_16,axiom,
    ( ~ incident_c(A,B)
    | part_of(ax0_sk4(B,A),B)
    | end_point(A,B) ) ).

cnf(end_point_defn_17,axiom,
    ( ~ incident_c(A,B)
    | incident_c(A,ax0_sk3(B,A))
    | end_point(A,B) ) ).

cnf(end_point_defn_18,axiom,
    ( ~ incident_c(A,B)
    | incident_c(A,ax0_sk4(B,A))
    | end_point(A,B) ) ).

cnf(end_point_defn_19,axiom,
    ( ~ incident_c(A,B)
    | ~ part_of(ax0_sk3(B,A),ax0_sk4(B,A))
    | end_point(A,B) ) ).

cnf(end_point_defn_20,axiom,
    ( ~ incident_c(A,B)
    | ~ part_of(ax0_sk4(B,A),ax0_sk3(B,A))
    | end_point(A,B) ) ).

cnf(inner_point_defn_21,axiom,
    ( ~ inner_point(A,B)
    | incident_c(A,B) ) ).

cnf(inner_point_defn_22,axiom,
    ( ~ inner_point(A,B)
    | ~ end_point(A,B) ) ).

cnf(inner_point_defn_23,axiom,
    ( ~ incident_c(A,B)
    | end_point(A,B)
    | inner_point(A,B) ) ).

cnf(meet_defn_24,axiom,
    ( ~ meet(A,B,C)
    | incident_c(A,B) ) ).

cnf(meet_defn_25,axiom,
    ( ~ meet(A,B,C)
    | incident_c(A,C) ) ).

cnf(meet_defn_26,axiom,
    ( ~ meet(A,B,C)
    | ~ incident_c(D,B)
    | ~ incident_c(D,C)
    | end_point(D,B) ) ).

cnf(meet_defn_27,axiom,
    ( ~ meet(A,B,C)
    | ~ incident_c(D,B)
    | ~ incident_c(D,C)
    | end_point(D,C) ) ).

cnf(meet_defn_28,axiom,
    ( ~ incident_c(A,B)
    | ~ incident_c(A,C)
    | incident_c(ax0_sk5(C,B,A),B)
    | meet(A,B,C) ) ).

cnf(meet_defn_29,axiom,
    ( ~ incident_c(A,B)
    | ~ incident_c(A,C)
    | incident_c(ax0_sk5(C,B,A),C)
    | meet(A,B,C) ) ).

cnf(meet_defn_30,axiom,
    ( ~ incident_c(A,B)
    | ~ incident_c(A,C)
    | ~ end_point(ax0_sk5(C,B,A),B)
    | ~ end_point(ax0_sk5(C,B,A),C)
    | meet(A,B,C) ) ).

cnf(closed_defn_31,axiom,
    ( ~ closed(A)
    | ~ end_point(B,A) ) ).

cnf(closed_defn_32,axiom,
    ( end_point(ax0_sk6(A),A)
    | closed(A) ) ).

cnf(open_defn_33,axiom,
    ( ~ open(A)
    | end_point(ax0_sk7(A),A) ) ).

cnf(open_defn_34,axiom,
    ( ~ end_point(A,B)
    | open(B) ) ).

cnf(c1_35,axiom,
    ( ~ part_of(A,B)
    | A = B
    | open(A) ) ).

cnf(c2_36,axiom,
    ( ~ part_of(A,B)
    | ~ part_of(C,B)
    | ~ part_of(D,B)
    | ~ end_point(E,A)
    | ~ end_point(E,C)
    | ~ end_point(E,D)
    | part_of(C,D)
    | part_of(D,C)
    | part_of(A,C)
    | part_of(C,A)
    | part_of(A,D)
    | part_of(D,A) ) ).

cnf(c3_37,axiom,
    inner_point(ax0_sk8(A),A) ).

cnf(c4_38,axiom,
    ( ~ inner_point(A,B)
    | meet(A,ax0_sk9(A,B),ax0_sk10(A,B)) ) ).

cnf(c4_39,axiom,
    ( ~ inner_point(A,B)
    | B = sum(ax0_sk9(A,B),ax0_sk10(A,B)) ) ).

cnf(c5_40,axiom,
    ( ~ end_point(A,B)
    | ~ end_point(C,B)
    | ~ end_point(D,B)
    | A = C
    | A = D
    | C = D ) ).

cnf(c6_41,axiom,
    ( ~ end_point(A,B)
    | end_point(ax0_sk11(A,B),B) ) ).

cnf(c6_42,axiom,
    ( ~ end_point(A,B)
    | A != ax0_sk11(A,B) ) ).

cnf(c7_43,axiom,
    ( ~ closed(A)
    | ~ meet(B,C,D)
    | A != sum(C,D)
    | ~ end_point(E,C)
    | meet(E,C,D) ) ).

cnf(c8_44,axiom,
    ( ~ meet(A,B,C)
    | ax0_sk12(C,B) = sum(B,C) ) ).

cnf(c9_45,axiom,
    ( incident_c(ax0_sk13(A,B),B)
    | incident_c(ax0_sk13(A,B),A)
    | B = A ) ).

cnf(c9_46,axiom,
    ( incident_c(ax0_sk13(A,B),B)
    | ~ incident_c(ax0_sk13(A,B),B)
    | B = A ) ).

cnf(c9_47,axiom,
    ( ~ incident_c(ax0_sk13(A,B),A)
    | incident_c(ax0_sk13(A,B),A)
    | B = A ) ).

cnf(c9_48,axiom,
    ( ~ incident_c(ax0_sk13(A,B),A)
    | ~ incident_c(ax0_sk13(A,B),B)
    | B = A ) ).

%--------------------------------------------------------------------------

```

### ./GEO004-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004-1 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Betweenness for simple curves
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   1 nHn;   6 RR)
%            Number of literals    :   16 (   2 equ;  10 neg)
%            Maximal clause size   :    6 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-4 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 4-4 aty)
%            Number of variables   :   25 (   2 sgn)
% SPC      : 

% Comments : Requires GEO004-0.ax
%          : Created by tptp2X -f tptp -t clausify:otter GEO004+1.ax
%--------------------------------------------------------------------------
cnf(between_c_defn_1,axiom,
    ( ~ between_c(A,B,C,D)
    | B != D ) ).

cnf(between_c_defn_2,axiom,
    ( ~ between_c(A,B,C,D)
    | part_of(ax1_sk1(D,C,B,A),A) ) ).

cnf(between_c_defn_3,axiom,
    ( ~ between_c(A,B,C,D)
    | end_point(B,ax1_sk1(D,C,B,A)) ) ).

cnf(between_c_defn_4,axiom,
    ( ~ between_c(A,B,C,D)
    | end_point(D,ax1_sk1(D,C,B,A)) ) ).

cnf(between_c_defn_5,axiom,
    ( ~ between_c(A,B,C,D)
    | inner_point(C,ax1_sk1(D,C,B,A)) ) ).

cnf(between_c_defn_6,axiom,
    ( A = B
    | ~ part_of(C,D)
    | ~ end_point(A,C)
    | ~ end_point(B,C)
    | ~ inner_point(E,C)
    | between_c(D,A,E,B) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004-2 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Oriented curves
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   42 (   2 unt;  20 nHn;  37 RR)
%            Number of literals    :  129 (  17 equ;  64 neg)
%            Maximal clause size   :    6 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    9 (   8 usr;   0 prp; 1-4 aty)
%            Number of functors    :   11 (  11 usr;   0 con; 1-5 aty)
%            Number of variables   :  125 (   5 sgn)
% SPC      : 

% Comments : Requires GEO004-0.ax GEO004-1.ax
%          : Created by tptp2X -f tptp -t clausify:otter GEO004+2.ax
%--------------------------------------------------------------------------
cnf(between_o_defn_1,axiom,
    ( ~ between_o(A,B,C,D)
    | ordered_by(A,B,C)
    | ordered_by(A,D,C) ) ).

cnf(between_o_defn_2,axiom,
    ( ~ between_o(A,B,C,D)
    | ordered_by(A,B,C)
    | ordered_by(A,C,B) ) ).

cnf(between_o_defn_3,axiom,
    ( ~ between_o(A,B,C,D)
    | ordered_by(A,C,D)
    | ordered_by(A,D,C) ) ).

cnf(between_o_defn_4,axiom,
    ( ~ between_o(A,B,C,D)
    | ordered_by(A,C,D)
    | ordered_by(A,C,B) ) ).

cnf(between_o_defn_5,axiom,
    ( ~ ordered_by(A,B,C)
    | ~ ordered_by(A,C,D)
    | between_o(A,B,C,D) ) ).

cnf(between_o_defn_6,axiom,
    ( ~ ordered_by(A,B,C)
    | ~ ordered_by(A,C,D)
    | between_o(A,D,C,B) ) ).

cnf(start_point_defn_7,axiom,
    ( ~ start_point(A,B)
    | incident_o(A,B) ) ).

cnf(start_point_defn_8,axiom,
    ( ~ start_point(A,B)
    | A = C
    | ~ incident_o(C,B)
    | ordered_by(B,A,C) ) ).

cnf(start_point_defn_9,axiom,
    ( ~ incident_o(A,B)
    | A != ax2_sk1(B,A)
    | start_point(A,B) ) ).

cnf(start_point_defn_10,axiom,
    ( ~ incident_o(A,B)
    | incident_o(ax2_sk1(B,A),B)
    | start_point(A,B) ) ).

cnf(start_point_defn_11,axiom,
    ( ~ incident_o(A,B)
    | ~ ordered_by(B,A,ax2_sk1(B,A))
    | start_point(A,B) ) ).

cnf(finish_point_defn_12,axiom,
    ( ~ finish_point(A,B)
    | incident_o(A,B) ) ).

cnf(finish_point_defn_13,axiom,
    ( ~ finish_point(A,B)
    | A = C
    | ~ incident_o(C,B)
    | ordered_by(B,C,A) ) ).

cnf(finish_point_defn_14,axiom,
    ( ~ incident_o(A,B)
    | A != ax2_sk2(B,A)
    | finish_point(A,B) ) ).

cnf(finish_point_defn_15,axiom,
    ( ~ incident_o(A,B)
    | incident_o(ax2_sk2(B,A),B)
    | finish_point(A,B) ) ).

cnf(finish_point_defn_16,axiom,
    ( ~ incident_o(A,B)
    | ~ ordered_by(B,ax2_sk2(B,A),A)
    | finish_point(A,B) ) ).

cnf(o1_17,axiom,
    ( ~ ordered_by(A,B,C)
    | incident_o(B,A) ) ).

cnf(o1_18,axiom,
    ( ~ ordered_by(A,B,C)
    | incident_o(C,A) ) ).

cnf(o2_19,axiom,
    open(ax2_sk3(A)) ).

cnf(o2_20,axiom,
    ( ~ incident_o(A,B)
    | incident_c(A,ax2_sk3(B)) ) ).

cnf(o2_21,axiom,
    ( ~ incident_c(A,ax2_sk3(B))
    | incident_o(A,B) ) ).

cnf(o3_22,axiom,
    ( ~ between_o(A,B,C,D)
    | ~ incident_o(E,A)
    | incident_c(E,ax2_sk4(A,D,C,B)) ) ).

cnf(o3_23,axiom,
    ( ~ between_o(A,B,C,D)
    | ~ incident_c(E,ax2_sk4(A,D,C,B))
    | incident_o(E,A) ) ).

cnf(o3_24,axiom,
    ( ~ between_o(A,B,C,D)
    | between_c(ax2_sk4(A,D,C,B),B,C,D) ) ).

cnf(o3_25,axiom,
    ( incident_o(ax2_sk5(A,B,C,D,E),B)
    | incident_c(ax2_sk5(A,B,C,D,E),A)
    | ~ between_c(A,E,D,C)
    | between_o(B,E,D,C) ) ).

cnf(o3_26,axiom,
    ( incident_o(ax2_sk5(A,B,C,D,E),B)
    | ~ incident_o(ax2_sk5(A,B,C,D,E),B)
    | ~ between_c(A,E,D,C)
    | between_o(B,E,D,C) ) ).

cnf(o3_27,axiom,
    ( ~ incident_c(ax2_sk5(A,B,C,D,E),A)
    | incident_c(ax2_sk5(A,B,C,D,E),A)
    | ~ between_c(A,E,D,C)
    | between_o(B,E,D,C) ) ).

cnf(o3_28,axiom,
    ( ~ incident_c(ax2_sk5(A,B,C,D,E),A)
    | ~ incident_o(ax2_sk5(A,B,C,D,E),B)
    | ~ between_c(A,E,D,C)
    | between_o(B,E,D,C) ) ).

cnf(o4_29,axiom,
    start_point(ax2_sk6(A),A) ).

cnf(o5_30,axiom,
    ( ~ open(A)
    | B = C
    | ~ incident_c(B,A)
    | ~ incident_c(C,A)
    | ~ incident_o(D,ax2_sk7(A,C,B))
    | incident_c(D,A) ) ).

cnf(o5_31,axiom,
    ( ~ open(A)
    | B = C
    | ~ incident_c(B,A)
    | ~ incident_c(C,A)
    | ~ incident_c(D,A)
    | incident_o(D,ax2_sk7(A,C,B)) ) ).

cnf(o5_32,axiom,
    ( ~ open(A)
    | B = C
    | ~ incident_c(B,A)
    | ~ incident_c(C,A)
    | ordered_by(ax2_sk7(A,C,B),B,C) ) ).

cnf(o6_33,axiom,
    ( ordered_by(A,ax2_sk8(B,A),ax2_sk9(B,A))
    | ordered_by(B,ax2_sk8(B,A),ax2_sk9(B,A))
    | A = B ) ).

cnf(o6_34,axiom,
    ( ordered_by(A,ax2_sk8(B,A),ax2_sk9(B,A))
    | ~ ordered_by(A,ax2_sk8(B,A),ax2_sk9(B,A))
    | A = B ) ).

cnf(o6_35,axiom,
    ( ~ ordered_by(A,ax2_sk8(A,B),ax2_sk9(A,B))
    | ordered_by(A,ax2_sk8(A,B),ax2_sk9(A,B))
    | B = A ) ).

cnf(o6_36,axiom,
    ( ~ ordered_by(A,ax2_sk8(A,B),ax2_sk9(A,B))
    | ~ ordered_by(B,ax2_sk8(A,B),ax2_sk9(A,B))
    | B = A ) ).

cnf(underlying_curve_defn_37,axiom,
    ( A != underlying_curve(B)
    | ~ incident_o(C,B)
    | incident_c(C,A) ) ).

cnf(underlying_curve_defn_38,axiom,
    ( A != underlying_curve(B)
    | ~ incident_c(C,A)
    | incident_o(C,B) ) ).

cnf(underlying_curve_defn_39,axiom,
    ( incident_o(ax2_sk10(A,B),A)
    | incident_c(ax2_sk10(A,B),B)
    | B = underlying_curve(A) ) ).

cnf(underlying_curve_defn_40,axiom,
    ( incident_o(ax2_sk10(A,B),A)
    | ~ incident_o(ax2_sk10(A,B),A)
    | B = underlying_curve(A) ) ).

cnf(underlying_curve_defn_41,axiom,
    ( ~ incident_c(ax2_sk10(A,B),B)
    | incident_c(ax2_sk10(A,B),B)
    | B = underlying_curve(A) ) ).

cnf(underlying_curve_defn_42,axiom,
    ( ~ incident_c(ax2_sk10(A,B),B)
    | ~ incident_o(ax2_sk10(A,B),A)
    | B = underlying_curve(A) ) ).

%--------------------------------------------------------------------------

```

### ./GEO004-3.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO004-3 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Axioms   : Trajectories
% Version  : [EHK99] axioms.
% English  :

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [EHK99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   14 (   1 unt;   0 nHn;  12 RR)
%            Number of literals    :   29 (   1 equ;  16 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :    5 (   5 usr;   0 con; 1-2 aty)
%            Number of variables   :   34 (   2 sgn)
% SPC      : 

% Comments : Requires GEO004-0.ax GEO004-1.ax GEO004-2.ax
%          : Created by tptp2X -f tptp -t clausify:otter GEO004+3.ax
%--------------------------------------------------------------------------
cnf(connect_defn_1,axiom,
    ( ~ connect(A,B,C)
    | once(at_the_same_time(at(A,C),at(B,C))) ) ).

cnf(connect_defn_2,axiom,
    ( ~ once(at_the_same_time(at(A,B),at(C,B)))
    | connect(A,C,B) ) ).

cnf(symmetry_of_at_the_same_time_3,axiom,
    ( ~ once(at_the_same_time(A,B))
    | once(at_the_same_time(B,A)) ) ).

cnf(symmetry_of_at_the_same_time_4,axiom,
    ( ~ once(at_the_same_time(A,B))
    | once(at_the_same_time(B,A)) ) ).

cnf(assciativity_of_at_the_same_time_5,axiom,
    ( ~ once(at_the_same_time(at_the_same_time(A,B),C))
    | once(at_the_same_time(A,at_the_same_time(B,C))) ) ).

cnf(assciativity_of_at_the_same_time_6,axiom,
    ( ~ once(at_the_same_time(A,at_the_same_time(B,C)))
    | once(at_the_same_time(at_the_same_time(A,B),C)) ) ).

cnf(idempotence_of_at_the_same_time_7,axiom,
    ( ~ once(A)
    | once(at_the_same_time(A,A)) ) ).

cnf(conjunction_at_the_same_time_8,axiom,
    ( ~ once(at_the_same_time(A,B))
    | once(A) ) ).

cnf(conjunction_at_the_same_time_9,axiom,
    ( ~ once(at_the_same_time(A,B))
    | once(B) ) ).

cnf(at_on_trajectory_10,axiom,
    ( ~ once(at(A,B))
    | incident_o(B,trajectory_of(A)) ) ).

cnf(at_on_trajectory_11,axiom,
    ( ~ incident_o(A,trajectory_of(B))
    | once(at(B,A)) ) ).

cnf(trajectories_are_oriented_curves_12,axiom,
    trajectory_of(A) = ax3_sk1(A) ).

cnf(homogeneous_behaviour_13,axiom,
    ( ~ once(at_the_same_time(at(A,B),at(C,D)))
    | ~ once(at_the_same_time(at(A,E),at(C,F)))
    | ~ ordered_by(trajectory_of(A),B,E)
    | ~ ordered_by(trajectory_of(C),F,D) ) ).

cnf(localization_14,axiom,
    ( ~ once(A)
    | once(at_the_same_time(A,at(B,ax3_sk2(B,A)))) ) ).

%--------------------------------------------------------------------------

```

### ./GEO005-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GEO005-0 : TPTP v8.2.0. Released v2.7.0.
% Domain   : Geometry (Hilbert)
% Axioms   : Hilbert geometry axioms, adapted to respect multi-sortedness
% Version  : [Cla03] axioms.
% English  :

% Refs     : [Ben92] Benana992), Recognising Unnecessary Clauses in Res
%          : [Cla03] Claessen (2003), Email to G. Sutcliffe
% Source   : [Cla03]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   31 (   1 unt;  18 nHn;  31 RR)
%            Number of literals    :  174 (  43 equ; 103 neg)
%            Maximal clause size   :   16 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :   10 (  10 usr;   1 con; 0-3 aty)
%            Number of variables   :   70 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Axiom 1 : For any two distinct points, there is a unique line through
%----them.
cnf(axiom_G1A,axiom,
    ( point_on_line(Z1,line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1B,axiom,
    ( point_on_line(Z2,line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1C,axiom,
    ( line(line_from_to(Z1,Z2))
    | Z1 = Z2
    | ~ point(Z1)
    | ~ point(Z2) ) ).

cnf(axiom_G1D,axiom,
    ( ~ point_on_line(Z1,Y3)
    | Z1 = Z2
    | ~ point_on_line(Z2,Y3)
    | Y3 = Y4
    | ~ point_on_line(Z1,Y4)
    | ~ point_on_line(Z2,Y4)
    | ~ point(Z1)
    | ~ point(Z2)
    | ~ line(Y3)
    | ~ line(Y4) ) ).

%----For any line, there are at least two points on the line.
cnf(axiom_G2A,axiom,
    ( point_on_line(point_1_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G2B,axiom,
    ( point_on_line(point_2_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G2C,axiom,
    ( point(point_1_on_line(Y1))
    | ~ line(Y1) ) ).

cnf(axiom_G2D,axiom,
    ( point(point_2_on_line(Y1))
    | ~ line(Y1) ) ).

cnf(axiom_G2E,axiom,
    ( point_1_on_line(Y1) != point_2_on_line(Y1)
    | ~ line(Y1) ) ).

%----For any line, there is a point not on the line.
cnf(axiom_G3A,axiom,
    ( ~ point_on_line(a_point_not_on_line(Y1),Y1)
    | ~ line(Y1) ) ).

cnf(axiom_G3B,axiom,
    ( point(a_point_not_on_line(Y1))
    | ~ line(Y1) ) ).

%----There exists at least one line
cnf(axiom_G4A,axiom,
    line(at_least_one_line) ).

%----For any plane there is a point on the plane.
cnf(axiom_G5A,axiom,
    ( ~ plane(Z1)
    | point_on_plane(a_point_on_plane(Z1),Z1) ) ).

cnf(axiom_G5B,axiom,
    ( ~ plane(Z1)
    | point(a_point_on_plane(Z1)) ) ).

%----For any plane there is a point not on the plane.
cnf(axiom_G6A,axiom,
    ( ~ plane(Z1)
    | ~ point_on_plane(a_point_not_on_plane(Z1),Z1) ) ).

cnf(axiom_G6B,axiom,
    ( ~ plane(Z1)
    | point(a_point_not_on_plane(Z1)) ) ).

%----For any three non-collinear points there is a unique plane through
%----them.
cnf(axiom_G7A,axiom,
    ( point_on_plane(X1,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7B,axiom,
    ( point_on_plane(X2,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7C,axiom,
    ( point_on_plane(X3,plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7D,axiom,
    ( plane(plane_for_points(X1,X2,X3))
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3 ) ).

cnf(axiom_G7E,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | collinear(X1,X2,X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X2,Z1)
    | ~ point_on_plane(X3,Z1)
    | ~ plane(Z1)
    | ~ point_on_plane(X1,Z2)
    | ~ point_on_plane(X2,Z2)
    | ~ point_on_plane(X3,Z2)
    | ~ plane(Z2)
    | Z1 = Z2 ) ).

%----If two points of a line are in the same plane then every point
%----of that line is in the plane.
cnf(axiom_G8A,axiom,
    ( ~ point_on_line(X1,Y1)
    | ~ point_on_line(X2,Y1)
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X2,Z1)
    | ~ plane(Z1)
    | ~ point(X1)
    | ~ point(X2)
    | ~ line(Y1)
    | X1 = X2
    | line_on_plane(Y1,Z1) ) ).

%----If two planes have a point in common they have at least one more
%----point in common.
cnf(axiom_G9A,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X1,Z2)
    | ~ point(X1)
    | point_on_plane(common_point_on_planes(Z1,Z2,X1),Z1) ) ).

cnf(axiom_G9B,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X1,Z2)
    | ~ point(X1)
    | point_on_plane(common_point_on_planes(Z1,Z2,X1),Z2) ) ).

cnf(axiom_G9C,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X1,Z2)
    | ~ point(X1)
    | point(common_point_on_planes(Z1,Z2,X1)) ) ).

cnf(axiom_G9D,axiom,
    ( ~ plane(Z1)
    | ~ plane(Z2)
    | Z1 = Z2
    | ~ point_on_plane(X1,Z1)
    | ~ point_on_plane(X1,Z2)
    | ~ point(X1)
    | X1 != common_point_on_planes(Z1,Z2,X1) ) ).

%----Three distinct points are collinear if and only if there is a line
%----through them.
cnf(axiom_G10A,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | point_on_line(X1,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10B,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | point_on_line(X2,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10C,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | point_on_line(X3,line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10D,axiom,
    ( ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | line(line_through_3_points(X1,X2,X3))
    | ~ collinear(X1,X2,X3) ) ).

cnf(axiom_G10E,axiom,
    ( collinear(X1,X2,X3)
    | ~ point_on_line(X1,Y)
    | ~ point_on_line(X2,Y)
    | ~ point_on_line(X3,Y)
    | ~ point(X1)
    | ~ point(X2)
    | ~ point(X3)
    | X1 = X2
    | X1 = X3
    | X2 = X3
    | ~ line(Y) ) ).

%--------------------------------------------------------------------------

```

### ./GEO006+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+0 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Apartness geometry
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   14 (   3 unt;   0 def)
%            Number of atoms       :   35 (   0 equ)
%            Maximal formula atoms :    6 (   2 avg)
%            Number of connectives :   28 (   7   ~;   9   |;   1   &)
%                                         (   0 <=>;  11  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   33 (  33   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Apartness for distinct points, distinct lines, convergent lines
fof(apart1,axiom,
    ! [X] : ~ distinct_points(X,X) ).

fof(apart2,axiom,
    ! [X] : ~ distinct_lines(X,X) ).

fof(apart3,axiom,
    ! [X] : ~ convergent_lines(X,X) ).

fof(apart4,axiom,
    ! [X,Y,Z] :
      ( distinct_points(X,Y)
     => ( distinct_points(X,Z)
        | distinct_points(Y,Z) ) ) ).

fof(apart5,axiom,
    ! [X,Y,Z] :
      ( distinct_lines(X,Y)
     => ( distinct_lines(X,Z)
        | distinct_lines(Y,Z) ) ) ).

fof(ax6,axiom,
    ! [X,Y,Z] :
      ( convergent_lines(X,Y)
     => ( convergent_lines(X,Z)
        | convergent_lines(Y,Z) ) ) ).

%----Connecting lines and intersection points
fof(ci1,axiom,
    ! [X,Y] :
      ( distinct_points(X,Y)
     => ~ apart_point_and_line(X,line_connecting(X,Y)) ) ).

fof(ci2,axiom,
    ! [X,Y] :
      ( distinct_points(X,Y)
     => ~ apart_point_and_line(Y,line_connecting(X,Y)) ) ).

fof(ci3,axiom,
    ! [X,Y] :
      ( convergent_lines(X,Y)
     => ~ apart_point_and_line(intersection_point(X,Y),X) ) ).

fof(ci4,axiom,
    ! [X,Y] :
      ( convergent_lines(X,Y)
     => ~ apart_point_and_line(intersection_point(X,Y),Y) ) ).

%----Constructive uniqueness axiom for lines and points
fof(cu1,axiom,
    ! [X,Y,U,V] :
      ( ( distinct_points(X,Y)
        & distinct_lines(U,V) )
     => ( apart_point_and_line(X,U)
        | apart_point_and_line(X,V)
        | apart_point_and_line(Y,U)
        | apart_point_and_line(Y,V) ) ) ).

%----Compatibility of equality with apartness and convergence
fof(ceq1,axiom,
    ! [X,Y,Z] :
      ( apart_point_and_line(X,Y)
     => ( distinct_points(X,Z)
        | apart_point_and_line(Z,Y) ) ) ).

fof(ceq2,axiom,
    ! [X,Y,Z] :
      ( apart_point_and_line(X,Y)
     => ( distinct_lines(Y,Z)
        | apart_point_and_line(X,Z) ) ) ).

fof(ceq3,axiom,
    ! [X,Y,Z] :
      ( convergent_lines(X,Y)
     => ( distinct_lines(Y,Z)
        | convergent_lines(X,Z) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+1 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Projective geometry
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    1 (   0 unt;   0 def)
%            Number of atoms       :    2 (   0 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   4 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    2 (   2   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+0
%------------------------------------------------------------------------------
fof(p1,axiom,
    ! [X,Y] :
      ( distinct_lines(X,Y)
     => convergent_lines(X,Y) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+2 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Affine geometry
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   2 unt;   0 def)
%            Number of atoms       :    6 (   0 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :    5 (   2   ~;   2   |;   0   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :    7 (   7   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+0
%------------------------------------------------------------------------------
%----Axioms for constructed parallels
fof(cp1,axiom,
    ! [X,Y] : ~ convergent_lines(parallel_through_point(Y,X),Y) ).

fof(cp2,axiom,
    ! [X,Y] : ~ apart_point_and_line(X,parallel_through_point(Y,X)) ).

%----Constructive uniqueness axiom for parallels
fof(cup1,axiom,
    ! [X,Y,Z] :
      ( distinct_lines(Y,Z)
     => ( apart_point_and_line(X,Y)
        | apart_point_and_line(X,Z)
        | convergent_lines(Y,Z) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+3 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Orthogonality
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   2 unt;   0 def)
%            Number of atoms       :   15 (   0 equ)
%            Maximal formula atoms :    6 (   3 avg)
%            Number of connectives :   12 (   2   ~;   5   |;   3   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   6 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   13 (  13   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+0, GEO006+2
%------------------------------------------------------------------------------
%----Compatibility of convergence and unorthogonality
fof(occu1,axiom,
    ! [L,M] :
      ( convergent_lines(L,M)
      | unorthogonal_lines(L,M) ) ).

%----Apartness axiom for the conjunction of convergence and unorthogonality
fof(oac1,axiom,
    ! [L,M,N] :
      ( ( convergent_lines(L,M)
        & unorthogonal_lines(L,M) )
     => ( ( convergent_lines(L,N)
          & unorthogonal_lines(L,N) )
        | ( convergent_lines(M,N)
          & unorthogonal_lines(M,N) ) ) ) ).

%----Axioms for the orthogonal construction
fof(ooc1,axiom,
    ! [A,L] : ~ unorthogonal_lines(orthogonal_through_point(L,A),L) ).

fof(ooc2,axiom,
    ! [A,L] : ~ apart_point_and_line(A,orthogonal_through_point(L,A)) ).

%----Constructive uniqueness axiom for orthogonals
fof(ouo1,axiom,
    ! [A,L,M,N] :
      ( distinct_lines(L,M)
     => ( apart_point_and_line(A,L)
        | apart_point_and_line(A,M)
        | unorthogonal_lines(L,N)
        | unorthogonal_lines(M,N) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+4 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Classical orthogonality
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   0 unt;   0 def)
%            Number of atoms       :   11 (   0 equ)
%            Maximal formula atoms :    6 (   3 avg)
%            Number of connectives :   20 (  12   ~;   3   |;   3   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   7 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    8 (   8   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+0, GEO006+2 ????????
%------------------------------------------------------------------------------
%----Incompatibility of parallelism and orthogonality
fof(coipo1,axiom,
    ! [L,M] :
      ~ ( ~ convergent_lines(L,M)
        & ~ unorthogonal_lines(L,M) ) ).

%----Transitivity of nonobliqueness
fof(cotno1,axiom,
    ! [L,M,N] :
      ( ( ( ~ convergent_lines(L,M)
          | ~ unorthogonal_lines(L,M) )
        & ( ~ convergent_lines(L,N)
          | ~ unorthogonal_lines(L,N) ) )
     => ( ~ convergent_lines(M,N)
        | ~ unorthogonal_lines(M,N) ) ) ).

%----Uniqueness axiom for orthogonality
fof(couo1,axiom,
    ! [L,M,N] :
      ( ( ~ unorthogonal_lines(L,M)
        & ~ unorthogonal_lines(L,N) )
     => ~ convergent_lines(M,N) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+5.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+5 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Rules of construction
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   0 unt;   0 def)
%            Number of atoms       :   14 (   0 equ)
%            Maximal formula atoms :    4 (   3 avg)
%            Number of connectives :   10 (   0   ~;   0   |;   6   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   6 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 2-2 aty)
%            Number of variables   :    8 (   8   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+[0-4]
%------------------------------------------------------------------------------
%----Connecting line of points A and B
fof(con1,axiom,
    ! [A,B] :
      ( ( point(A)
        & point(B)
        & distinct_points(A,B) )
     => line(line_connecting(A,B)) ) ).

%----Intersection point of lines L and M
fof(int1,axiom,
    ! [L,M] :
      ( ( line(L)
        & line(M)
        & convergent_lines(L,M) )
     => point(intersection_point(L,M)) ) ).

%----Parallel lines
fof(par1,axiom,
    ! [L,A] :
      ( ( line(L)
        & point(A) )
     => line(parallel_through_point(L,A)) ) ).

%----Orthogonal lines
fof(orth1,axiom,
    ! [L,A] :
      ( ( line(L)
        & point(A) )
     => line(orthogonal_through_point(L,A)) ) ).

%------------------------------------------------------------------------------

```

### ./GEO006+6.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO006+6 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Geometry definitions
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   0 unt;   0 def)
%            Number of atoms       :   10 (   0 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :   10 (   5   ~;   0   |;   0   &)
%                                         (   5 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   5 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   10 (  10   !;   0   ?)
% SPC      : 

% Comments : Requires GEO006+[0-5]
%------------------------------------------------------------------------------
fof(ax1,axiom,
    ! [X,Y] :
      ( equal_points(X,Y)
    <=> ~ distinct_points(X,Y) ) ).

fof(ax2,axiom,
    ! [X,Y] :
      ( equal_lines(X,Y)
    <=> ~ distinct_lines(X,Y) ) ).

fof(a3,axiom,
    ! [X,Y] :
      ( parallel_lines(X,Y)
    <=> ~ convergent_lines(X,Y) ) ).

fof(a4,axiom,
    ! [X,Y] :
      ( incident_point_and_line(X,Y)
    <=> ~ apart_point_and_line(X,Y) ) ).

fof(a5,axiom,
    ! [X,Y] :
      ( orthogonal_lines(X,Y)
    <=> ~ unorthogonal_lines(X,Y) ) ).

%------------------------------------------------------------------------------

```

### ./GEO007+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO007+0 : TPTP v8.2.0. Bugfixed v6.4.0.
% Domain   : Geometry (Constructive)
% Axioms   : Ordered affine geometry
% Version  : [vPl98] axioms.
% English  :

% Refs     : [vPl98] von Plato (1998), A Constructive Theory of Ordered Aff
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   31 (   7 unt;   0 def)
%            Number of atoms       :  102 (   0 equ)
%            Maximal formula atoms :   10 (   3 avg)
%            Number of connectives :   87 (  16   ~;  24   |;  25   &)
%                                         (   5 <=>;  17  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   6 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :   12 (  12 usr;   0 prp; 1-4 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :   71 (  71   !;   0   ?)
% SPC      : 

% Comments :
% Bugfixes : v6.4.0 - Fixed oag8.
%------------------------------------------------------------------------------
%----Abbreviations
fof(apt_def,axiom,
    ! [A,L] :
      ( apart_point_and_line(A,L)
    <=> ( left_apart_point(A,L)
        | left_apart_point(A,reverse_line(L)) ) ) ).

fof(con_def,axiom,
    ! [L,M] :
      ( convergent_lines(L,M)
    <=> ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) ) ) ).

fof(div_def,axiom,
    ! [A,B,L] :
      ( divides_points(L,A,B)
    <=> ( ( left_apart_point(A,L)
          & left_apart_point(B,reverse_line(L)) )
        | ( left_apart_point(A,reverse_line(L))
          & left_apart_point(B,L) ) ) ) ).

fof(bf_def,axiom,
    ! [L,A,B] :
      ( before_on_line(L,A,B)
    <=> ( distinct_points(A,B)
        & ~ ( left_apart_point(A,L)
            | left_apart_point(A,reverse_line(L)) )
        & ~ ( left_apart_point(B,L)
            | left_apart_point(B,reverse_line(L)) )
        & ~ unequally_directed_lines(L,line_connecting(A,B)) ) ) ).

fof(bet_def,axiom,
    ! [L,A,B,C] :
      ( between_on_line(L,A,B,C)
    <=> ( ( before_on_line(L,A,B)
          & before_on_line(L,B,C) )
        | ( before_on_line(L,C,B)
          & before_on_line(L,B,A) ) ) ) ).

%----General axioms for the basic concepts
fof(oag1,axiom,
    ! [A] : ~ distinct_points(A,A) ).

fof(oag2,axiom,
    ! [A,B,C] :
      ( distinct_points(A,B)
     => ( distinct_points(A,C)
        | distinct_points(B,C) ) ) ).

fof(oag3,axiom,
    ! [L] : ~ distinct_lines(L,L) ).

fof(oag4,axiom,
    ! [L,M,N] :
      ( distinct_lines(L,M)
     => ( distinct_lines(L,N)
        | distinct_lines(M,N) ) ) ).

fof(oag5,axiom,
    ! [L] : ~ unequally_directed_lines(L,L) ).

fof(oag6,axiom,
    ! [L,M,N] :
      ( unequally_directed_lines(L,M)
     => ( unequally_directed_lines(L,N)
        | unequally_directed_lines(M,N) ) ) ).

fof(oag7,axiom,
    ! [L,M,N] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( ( unequally_directed_lines(L,N)
          & unequally_directed_lines(L,reverse_line(N)) )
        | ( unequally_directed_lines(M,N)
          & unequally_directed_lines(M,reverse_line(N)) ) ) ) ).

fof(oag8,axiom,
    ! [L,M] :
      ( ( line(L)
        & line(M) )
     => ( unequally_directed_lines(L,M)
        | unequally_directed_lines(L,reverse_line(M)) ) ) ).

fof(oag9,axiom,
    ! [L,M] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( left_convergent_lines(L,M)
        | left_convergent_lines(L,reverse_line(M)) ) ) ).

fof(oag10,axiom,
    ! [A,L] :
      ~ ( left_apart_point(A,L)
        | left_apart_point(A,reverse_line(L)) ) ).

fof(oag11,axiom,
    ! [L,M] :
      ~ ( left_convergent_lines(L,M)
        | left_convergent_lines(L,reverse_line(M)) ) ).

%----Constructed objects
fof(oagco1,axiom,
    ! [A,B] :
      ( ( point(A)
        & point(B)
        & distinct_points(A,B) )
     => line(line_connecting(A,B)) ) ).

fof(oagco2,axiom,
    ! [L,M] :
      ( ( line(L)
        & line(M)
        & unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => point(intersection_point(L,M)) ) ).

fof(oagco3,axiom,
    ! [L,A] :
      ( ( point(A)
        & line(L) )
     => line(parallel_through_point(L,A)) ) ).

fof(oagco4,axiom,
    ! [L] :
      ( line(L)
     => line(reverse_line(L)) ) ).

fof(oagco5,axiom,
    ! [A,B] :
      ( distinct_points(A,B)
     => ( ~ apart_point_and_line(A,line_connecting(A,B))
        & ~ apart_point_and_line(B,line_connecting(A,B)) ) ) ).

fof(oagco6,axiom,
    ! [L,M] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( ~ apart_point_and_line(intersection_point(L,M),L)
        & ~ apart_point_and_line(intersection_point(L,M),M) ) ) ).

fof(oagco7,axiom,
    ! [A,L] : ~ apart_point_and_line(A,parallel_through_point(L,A)) ).

fof(oagco8,axiom,
    ! [L] : ~ distinct_lines(L,reverse_line(L)) ).

fof(oagco9,axiom,
    ! [A,B] : ~ unequally_directed_lines(line_connecting(A,B),reverse_line(line_connecting(B,A))) ).

fof(oagco10,axiom,
    ! [A,L] : ~ unequally_directed_lines(parallel_through_point(L,A),L) ).

%----Uniqueness axioms for the constructions
fof(oaguc1,axiom,
    ! [A,B,L,M] :
      ( ( distinct_points(A,B)
        & distinct_lines(L,M) )
     => ( left_apart_point(A,L)
        | left_apart_point(B,L)
        | left_apart_point(A,M)
        | left_apart_point(B,M)
        | left_apart_point(A,reverse_line(L))
        | left_apart_point(B,reverse_line(L))
        | left_apart_point(A,reverse_line(M))
        | left_apart_point(B,reverse_line(M)) ) ) ).

fof(oaguc2,axiom,
    ! [A,B,L] :
      ( ( distinct_points(A,B)
        & left_apart_point(A,L) )
     => ( left_apart_point(B,L)
        | left_convergent_lines(line_connecting(A,B),L) ) ) ).

%----Substitution axioms
fof(oagsub1,axiom,
    ! [A,B,L] :
      ( left_apart_point(A,L)
     => ( distinct_points(A,B)
        | left_apart_point(B,L) ) ) ).

fof(oagsub2,axiom,
    ! [A,L,M] :
      ( ( left_apart_point(A,L)
        & unequally_directed_lines(L,M) )
     => ( distinct_lines(L,M)
        | left_apart_point(A,reverse_line(M)) ) ) ).

fof(oagsub3,axiom,
    ! [L,M,N] :
      ( left_convergent_lines(L,M)
     => ( unequally_directed_lines(M,N)
        | left_convergent_lines(L,N) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO007+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO007+1 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Principles of a classical calculus of directed lines
% Version  : [vPl98] axioms.
% English  :

% Refs     : [vPl98] von Plato (1998), A Constructive Theory of Ordered Aff
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   1 unt;   0 def)
%            Number of atoms       :   21 (   0 equ)
%            Maximal formula atoms :    6 (   3 avg)
%            Number of connectives :   34 (  19   ~;   4   |;   6   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :   16 (  16   !;   0   ?)
% SPC      : 

% Comments : Requires GEO007+0
% Bugfixes : v6.4.0 - Fixed cld4.
%------------------------------------------------------------------------------
fof(cld1,axiom,
    ! [L] : ~ unequally_directed_lines(L,L) ).

fof(cld2,axiom,
    ! [L,M,N] :
      ( ( ~ unequally_directed_lines(L,M)
        & ~ unequally_directed_lines(L,N) )
     => ~ unequally_directed_lines(M,N) ) ).

fof(cld3,axiom,
    ! [A,B,L,M] :
      ( ~ ( unequally_directed_lines(L,M)
          & unequally_directed_lines(L,reverse_line(M)) )
    <=> ( ~ unequally_directed_lines(L,M)
        | ~ unequally_directed_lines(L,reverse_line(M)) ) ) ).

fof(cld3a,axiom,
    ! [L,M,N] :
      ( ( ( ~ unequally_directed_lines(L,M)
          | ~ unequally_directed_lines(L,reverse_line(M)) )
        & ( ~ unequally_directed_lines(L,N)
          | ~ unequally_directed_lines(L,reverse_line(N)) ) )
     => ( ~ unequally_directed_lines(M,N)
        | ~ unequally_directed_lines(M,reverse_line(N)) ) ) ).

fof(cld4,axiom,
    ! [L,M] :
      ( ( line(L)
        & line(M) )
     => ~ ( ~ unequally_directed_lines(L,M)
          & ~ unequally_directed_lines(L,reverse_line(M)) ) ) ).

fof(cld5,axiom,
    ! [L,M,N] :
      ( ~ unequally_directed_lines(L,reverse_line(M))
      & ( ~ unequally_directed_lines(L,reverse_line(N))
       => ~ unequally_directed_lines(M,N) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO008+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO008+0 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Geometry (Constructive)
% Axioms   : Apartness geometry
% Version  : [Li97] axioms.
% English  :

% Refs     : [Li98]  Li (1998), A Shorter and Intuitive Axiom to Replace th
%          : [Li97]  Li (1997), Replacing the Axioms for Connecting Lines a
%          : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   12 (   3 unt;   0 def)
%            Number of atoms       :   34 (   0 equ)
%            Maximal formula atoms :    6 (   2 avg)
%            Number of connectives :   25 (   3   ~;   9   |;   2   &)
%                                         (   0 <=>;  11  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   6 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   30 (  30   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Apartness for distinct points, distinct lines, convergent lines
fof(apart1,axiom,
    ! [X] : ~ distinct_points(X,X) ).

fof(apart2,axiom,
    ! [X] : ~ distinct_lines(X,X) ).

fof(apart3,axiom,
    ! [X] : ~ convergent_lines(X,X) ).

fof(apart4,axiom,
    ! [X,Y,Z] :
      ( distinct_points(X,Y)
     => ( distinct_points(X,Z)
        | distinct_points(Y,Z) ) ) ).

fof(apart5,axiom,
    ! [X,Y,Z] :
      ( distinct_lines(X,Y)
     => ( distinct_lines(X,Z)
        | distinct_lines(Y,Z) ) ) ).

fof(apart6,axiom,
    ! [X,Y,Z] :
      ( convergent_lines(X,Y)
     => ( convergent_lines(X,Z)
        | convergent_lines(Y,Z) ) ) ).

%----Connecting lines and intersection points
fof(con1,axiom,
    ! [X,Y,Z] :
      ( distinct_points(X,Y)
     => ( apart_point_and_line(Z,line_connecting(X,Y))
       => ( distinct_points(Z,X)
          & distinct_points(Z,Y) ) ) ) ).

fof(con2,axiom,
    ! [X,Y,Z] :
      ( convergent_lines(X,Y)
     => ( ( apart_point_and_line(Z,X)
          | apart_point_and_line(Z,Y) )
       => distinct_points(Z,intersection_point(X,Y)) ) ) ).

%----Constructive uniqueness axiom for lines and points
fof(cu1,axiom,
    ! [X,Y,U,V] :
      ( ( distinct_points(X,Y)
        & distinct_lines(U,V) )
     => ( apart_point_and_line(X,U)
        | apart_point_and_line(X,V)
        | apart_point_and_line(Y,U)
        | apart_point_and_line(Y,V) ) ) ).

%----Compatibility of equality with apartness and convergence
fof(ceq1,axiom,
    ! [X,Y,Z] :
      ( apart_point_and_line(X,Y)
     => ( distinct_points(X,Z)
        | apart_point_and_line(Z,Y) ) ) ).

fof(ceq2,axiom,
    ! [X,Y,Z] :
      ( apart_point_and_line(X,Y)
     => ( distinct_lines(Y,Z)
        | apart_point_and_line(X,Z) ) ) ).

fof(ceq3,axiom,
    ! [X,Y] :
      ( convergent_lines(X,Y)
     => distinct_lines(X,Y) ) ).

%------------------------------------------------------------------------------

```

### ./GEO009+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO009+0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Geometry (Constructive)
% Axioms   : Ordered affine geometry with definitions
% Version  : [vPl95] axioms.
% English  :

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
% Source   : [ILTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   36 (   6 unt;   0 def)
%            Number of atoms       :  109 (   0 equ)
%            Maximal formula atoms :   10 (   3 avg)
%            Number of connectives :   85 (  12   ~;  22   |;  24   &)
%                                         (  10 <=>;  17  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :   18 (  18 usr;   0 prp; 1-4 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :   81 (  81   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(a1_defns,axiom,
    ! [X,Y] :
      ( unequally_directed_opposite_lines(X,Y)
    <=> unequally_directed_lines(X,reverse_line(Y)) ) ).

fof(a2_defns,axiom,
    ! [X,Y] :
      ( right_apart_point(X,Y)
    <=> left_apart_point(X,reverse_line(Y)) ) ).

fof(a3_defns,axiom,
    ! [X,Y] :
      ( right_convergent_lines(X,Y)
    <=> left_convergent_lines(X,reverse_line(Y)) ) ).

fof(a4_defns,axiom,
    ! [X,Y] :
      ( equally_directed_lines(X,Y)
    <=> ~ unequally_directed_lines(X,Y) ) ).

fof(a5_defns,axiom,
    ! [X,Y] :
      ( equally_directed_opposite_lines(X,Y)
    <=> ~ unequally_directed_opposite_lines(X,Y) ) ).

fof(a6_defns,axiom,
    ! [A,L] :
      ( apart_point_and_line(A,L)
    <=> ( left_apart_point(A,L)
        | right_apart_point(A,L) ) ) ).

fof(a7_defns,axiom,
    ! [L,M] :
      ( convergent_lines(L,M)
    <=> ( unequally_directed_lines(L,M)
        & unequally_directed_opposite_lines(L,M) ) ) ).

fof(a8_defns,axiom,
    ! [A,B,L] :
      ( divides_points(L,A,B)
    <=> ( ( left_apart_point(A,L)
          & right_apart_point(B,L) )
        | ( right_apart_point(A,L)
          & left_apart_point(B,L) ) ) ) ).

fof(ax4_defns,axiom,
    ! [L,A,B] :
      ( before_on_line(L,A,B)
    <=> ( distinct_points(A,B)
        & incident_point_and_line(A,L)
        & incident_point_and_line(B,L)
        & equally_directed_lines(L,line_connecting(A,B)) ) ) ).

fof(a9_defns,axiom,
    ! [L,A,B,C] :
      ( between_on_line(L,A,B,C)
    <=> ( ( before_on_line(L,A,B)
          & before_on_line(L,B,C) )
        | ( before_on_line(L,C,B)
          & before_on_line(L,B,A) ) ) ) ).

fof(ax1_basics,axiom,
    ! [A] : ~ distinct_points(A,A) ).

fof(ax2_basics,axiom,
    ! [A,B,C] :
      ( distinct_points(A,B)
     => ( distinct_points(A,C)
        | distinct_points(B,C) ) ) ).

fof(ax3_basics,axiom,
    ! [L] : ~ distinct_lines(L,L) ).

fof(ax4_basics,axiom,
    ! [L,M,N] :
      ( distinct_lines(L,M)
     => ( distinct_lines(L,N)
        | distinct_lines(M,N) ) ) ).

fof(ax5_basics,axiom,
    ! [L] : equally_directed_lines(L,L) ).

fof(ax6_basics,axiom,
    ! [L,M,N] :
      ( unequally_directed_lines(L,M)
     => ( unequally_directed_lines(L,N)
        | unequally_directed_lines(M,N) ) ) ).

fof(ax7_basics,axiom,
    ! [L,M,N] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( ( unequally_directed_lines(L,N)
          & unequally_directed_lines(L,reverse_line(N)) )
        | ( unequally_directed_lines(M,N)
          & unequally_directed_lines(M,reverse_line(N)) ) ) ) ).

fof(ax8_basics,axiom,
    ! [L,M] :
      ( unequally_directed_lines(L,M)
      | unequally_directed_lines(L,reverse_line(M)) ) ).

fof(ax9_basics,axiom,
    ! [L,M] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( left_convergent_lines(L,M)
        | left_convergent_lines(L,reverse_line(M)) ) ) ).

fof(ax10_basics,axiom,
    ! [A,L] :
      ~ ( left_apart_point(A,L)
        | left_apart_point(A,reverse_line(L)) ) ).

fof(ax11_basics,axiom,
    ! [L,M] :
      ~ ( left_convergent_lines(L,M)
        | left_convergent_lines(L,reverse_line(M)) ) ).

fof(ax1_cons_objs,axiom,
    ! [A,B] :
      ( ( point(A)
        & point(B)
        & distinct_points(A,B) )
     => line(line_connecting(A,B)) ) ).

fof(ax2_cons_objs,axiom,
    ! [L,M] :
      ( ( line(L)
        & line(M)
        & unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => point(intersection_point(L,M)) ) ).

fof(ax3_cons_objs,axiom,
    ! [L,A] :
      ( ( point(A)
        & line(L) )
     => line(parallel_through_point(L,A)) ) ).

fof(ax4_cons_objs,axiom,
    ! [L] :
      ( line(L)
     => line(reverse_line(L)) ) ).

fof(ax5_cons_objs,axiom,
    ! [A,B] :
      ( distinct_points(A,B)
     => ( ~ apart_point_and_line(A,line_connecting(A,B))
        & ~ apart_point_and_line(B,line_connecting(A,B)) ) ) ).

fof(ax6_cons_objs,axiom,
    ! [L,M] :
      ( ( unequally_directed_lines(L,M)
        & unequally_directed_lines(L,reverse_line(M)) )
     => ( ~ apart_point_and_line(intersection_point(L,M),L)
        & ~ apart_point_and_line(intersection_point(L,M),M) ) ) ).

fof(ax7_cons_objs,axiom,
    ! [A,L] : ~ apart_point_and_line(A,parallel_through_point(L,A)) ).

fof(ax8_cons_objs,axiom,
    ! [L] : ~ distinct_lines(L,reverse_line(L)) ).

fof(ax9_cons_objs,axiom,
    ! [A,B] :
      ( distinct_points(A,B)
     => equally_directed_lines(line_connecting(A,B),reverse_line(line_connecting(B,A))) ) ).

fof(ax10_cons_objs,axiom,
    ! [A,L] : equally_directed_lines(parallel_through_point(L,A),L) ).

fof(ax1_uniq_cons,axiom,
    ! [A,B,L,M] :
      ( ( distinct_points(A,B)
        & distinct_lines(L,M) )
     => ( left_apart_point(A,L)
        | left_apart_point(B,L)
        | left_apart_point(A,M)
        | left_apart_point(B,M)
        | left_apart_point(A,reverse_line(L))
        | left_apart_point(B,reverse_line(L))
        | left_apart_point(A,reverse_line(M))
        | left_apart_point(B,reverse_line(M)) ) ) ).

fof(ax2_uniq_cons,axiom,
    ! [A,B,L] :
      ( ( distinct_points(A,B)
        & left_apart_point(A,L) )
     => ( left_apart_point(B,L)
        | left_convergent_lines(line_connecting(A,B),L) ) ) ).

fof(ax1_subs,axiom,
    ! [A,B,L] :
      ( left_apart_point(A,L)
     => ( distinct_points(A,B)
        | left_apart_point(B,L) ) ) ).

fof(ax2_subs,axiom,
    ! [A,L,M] :
      ( ( left_apart_point(A,L)
        & unequally_directed_lines(L,M) )
     => ( distinct_lines(L,M)
        | left_apart_point(A,reverse_line(M)) ) ) ).

fof(ax3_subs,axiom,
    ! [L,M,N] :
      ( left_convergent_lines(L,M)
     => ( unequally_directed_lines(M,N)
        | left_convergent_lines(L,N) ) ) ).

%------------------------------------------------------------------------------

```

### ./GEO010+0.ax

Very long 17016

### ./GEO010+1.ax

Very long 5517

### ./GEO011+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GEO011+0 : TPTP v8.2.0. Released v7.0.0.
% Domain   : Geometry
% Axioms   : Tarskian geometry
% Version  : [Urb16] axioms : Especial.
% English  :

% Refs     : [Urb16] Urban (2016), Email to Geoff Sutcliffe
%          : [BW17]  Beeson & Wos (2017), Finding Proofs in Tarskian Geomet
% Source   : [Urb16]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   1 unt;   0 def)
%            Number of atoms       :   27 (   3 equ)
%            Maximal formula atoms :    8 (   3 avg)
%            Number of connectives :   36 (  17   ~;  15   |;   4   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   16 (   8 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-4 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-5 aty)
%            Number of variables   :   30 (  30   !;   0   ?)
% SPC      : FOF_SAT_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(aA1,axiom,
    ! [X,Y] : s_e(X,Y,Y,X) ).

fof(aA2,axiom,
    ! [X,Y,Z,V,Z2,V2] :
      ( ~ s_e(X,Y,Z,V)
      | ~ s_e(X,Y,Z2,V2)
      | s_e(Z,V,Z2,V2) ) ).

fof(aA3,axiom,
    ! [X,Y,Z] :
      ( ~ s_e(X,Y,Z,Z)
      | X = Y ) ).

fof(aA4,axiom,
    ! [X,Y,W,V] :
      ( s_t(X,Y,ext(X,Y,W,V))
      & s_e(Y,ext(X,Y,W,V),W,V) ) ).

fof(aA5,axiom,
    ! [X,Y,X1,Y1,Z,Z1,V,V1] :
      ( ~ s_e(X,Y,X1,Y1)
      | ~ s_e(Y,Z,Y1,Z1)
      | ~ s_e(X,V,X1,V1)
      | ~ s_e(Y,V,Y1,V1)
      | ~ s_t(X,Y,Z)
      | ~ s_t(X1,Y1,Z1)
      | X = Y
      | s_e(Z,V,Z1,V1) ) ).

fof(aA6,axiom,
    ! [X,Y] :
      ( ~ s_t(X,Y,X)
      | X = Y ) ).

fof(aA7,axiom,
    ! [Xa,Xp,Xc,Xb,Xq] :
      ( ( ~ s_t(Xa,Xp,Xc)
        | ~ s_t(Xb,Xq,Xc)
        | s_t(Xp,ip(Xa,Xp,Xc,Xb,Xq),Xb) )
      & ( ~ s_t(Xa,Xp,Xc)
        | ~ s_t(Xb,Xq,Xc)
        | s_t(Xq,ip(Xa,Xp,Xc,Xb,Xq),Xa) ) ) ).

fof(aA8,axiom,
    ( ~ s_t(alpha,beta,gamma)
    & ~ s_t(beta,gamma,alpha)
    & ~ s_t(gamma,alpha,beta) ) ).

%------------------------------------------------------------------------------

```

### ./GEO012+0.ax

Very long 621

## Graph Theory

### ./GRA001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GRA001+0 : TPTP v8.2.0. Bugfixed v3.2.0.
% Domain   : Graph Theory
% Axioms   : Directed graphs and paths
% Version  : [TPTP] axioms : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   12 (   0 unt;   0 def)
%            Number of atoms       :   72 (  21 equ)
%            Maximal formula atoms :    9 (   6 avg)
%            Number of connectives :   66 (   6   ~;   3   |;  38   &)
%                                         (   2 <=>;  12  =>;   2  <=;   3 <~>)
%            Maximal formula depth :   13 (  10 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   11 (  10 usr;   1 prp; 0-3 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-2 aty)
%            Number of variables   :   48 (  39   !;   9   ?)
% SPC      : 

% Comments :
% Bugfixes : v3.2.0 - Added formula edge_ends_are_vertices.
%------------------------------------------------------------------------------
fof(no_loops,axiom,
    ! [E] :
      ( edge(E)
     => head_of(E) != tail_of(E) ) ).

fof(edge_ends_are_vertices,axiom,
    ! [E] :
      ( edge(E)
     => ( vertex(head_of(E))
        & vertex(tail_of(E)) ) ) ).

fof(complete_properties,axiom,
    ( complete
   => ! [V1,V2] :
        ( ( vertex(V1)
          & vertex(V2)
          & V1 != V2 )
       => ? [E] :
            ( edge(E)
            & ( ( V1 = head_of(E)
                & V2 = tail_of(E) )
            <~> ( V2 = head_of(E)
                & V1 = tail_of(E) ) ) ) ) ) ).

fof(path_defn,axiom,
    ! [V1,V2,P] :
      ( path(V1,V2,P)
     <= ( vertex(V1)
        & vertex(V2)
        & ? [E] :
            ( edge(E)
            & V1 = tail_of(E)
            & ( ( V2 = head_of(E)
                & P = path_cons(E,empty) )
              | ? [TP] :
                  ( path(head_of(E),V2,TP)
                  & P = path_cons(E,TP) ) ) ) ) ) ).

fof(path_properties,axiom,
    ! [V1,V2,P] :
      ( path(V1,V2,P)
     => ( vertex(V1)
        & vertex(V2)
        & ? [E] :
            ( edge(E)
            & V1 = tail_of(E)
            & ( ( V2 = head_of(E)
                & P = path_cons(E,empty) )
            <~> ? [TP] :
                  ( path(head_of(E),V2,TP)
                  & P = path_cons(E,TP) ) ) ) ) ) ).

fof(on_path_properties,axiom,
    ! [V1,V2,P,E] :
      ( ( path(V1,V2,P)
        & on_path(E,P) )
     => ( edge(E)
        & in_path(head_of(E),P)
        & in_path(tail_of(E),P) ) ) ).

fof(in_path_properties,axiom,
    ! [V1,V2,P,V] :
      ( ( path(V1,V2,P)
        & in_path(V,P) )
     => ( vertex(V)
        & ? [E] :
            ( on_path(E,P)
            & ( V = head_of(E)
              | V = tail_of(E) ) ) ) ) ).

fof(sequential_defn,axiom,
    ! [E1,E2] :
      ( sequential(E1,E2)
    <=> ( edge(E1)
        & edge(E2)
        & E1 != E2
        & head_of(E1) = tail_of(E2) ) ) ).

fof(precedes_defn,axiom,
    ! [P,V1,V2] :
      ( path(V1,V2,P)
     => ! [E1,E2] :
          ( precedes(E1,E2,P)
         <= ( on_path(E1,P)
            & on_path(E2,P)
            & ( sequential(E1,E2)
              | ? [E3] :
                  ( sequential(E1,E3)
                  & precedes(E3,E2,P) ) ) ) ) ) ).

fof(precedes_properties,axiom,
    ! [P,V1,V2] :
      ( path(V1,V2,P)
     => ! [E1,E2] :
          ( precedes(E1,E2,P)
         => ( on_path(E1,P)
            & on_path(E2,P)
            & ( sequential(E1,E2)
            <~> ? [E3] :
                  ( sequential(E1,E3)
                  & precedes(E3,E2,P) ) ) ) ) ) ).

fof(shortest_path_defn,axiom,
    ! [V1,V2,SP] :
      ( shortest_path(V1,V2,SP)
    <=> ( path(V1,V2,SP)
        & V1 != V2
        & ! [P] :
            ( path(V1,V2,P)
           => less_or_equal(length_of(SP),length_of(P)) ) ) ) ).

fof(shortest_path_properties,axiom,
    ! [V1,V2,E1,E2,P] :
      ( ( shortest_path(V1,V2,P)
        & precedes(E1,E2,P) )
     => ( ~ ? [E3] :
              ( tail_of(E3) = tail_of(E1)
              & head_of(E3) = head_of(E2) )
        & ~ precedes(E2,E1,P) ) ) ).

%------------------------------------------------------------------------------

```

## Group Theory

### ./GRP001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group theory (Monoids)
% Axioms   : Monoid axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   3 unt;   0 nHn;   3 RR)
%            Number of literals    :   14 (   1 equ;   8 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-2 aty)
%            Number of variables   :   20 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
%          : I cut down the [MOW76] group axioms for this.
%--------------------------------------------------------------------------
cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(right_identity,axiom,
    product(X,identity,X) ).

%----This axiom is called closure or totality in some axiomatisations
cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | Z = W ) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

%--------------------------------------------------------------------------

```

### ./GRP002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory (Semigroups)
% Axioms   : Semigroup axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   1 unt;   0 nHn;   3 RR)
%            Number of literals    :   12 (   1 equ;   8 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   18 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
%          : I cut down the [MOW76] group axioms for this.
%--------------------------------------------------------------------------
%----This axiom is called closure or totality in some axiomatisations
cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | Z = W ) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

%--------------------------------------------------------------------------

```

### ./GRP003+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP003+0 : TPTP v8.2.0. Released v2.5.0.
% Domain   : Group Theory
% Axioms   : Group theory axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : TPTP
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   5 unt;   0 def)
%            Number of atoms       :   16 (   1 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :    8 (   0   ~;   0   |;   5   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :   22 (  22   !;   0   ?)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
fof(left_identity,axiom,
    ! [X] : product(identity,X,X) ).

fof(right_identity,axiom,
    ! [X] : product(X,identity,X) ).

fof(left_inverse,axiom,
    ! [X] : product(inverse(X),X,identity) ).

fof(right_inverse,axiom,
    ! [X] : product(X,inverse(X),identity) ).

%----This axiom is called closure or totality in some axiomatisations
fof(total_function1,axiom,
    ! [X,Y] : product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
fof(total_function2,axiom,
    ! [W,X,Y,Z] :
      ( ( product(X,Y,Z)
        & product(X,Y,W) )
     => Z = W ) ).

fof(associativity1,axiom,
    ! [X,Y,Z,U,V,W] :
      ( ( product(X,Y,U)
        & product(Y,Z,V)
        & product(U,Z,W) )
     => product(X,V,W) ) ).

fof(associativity2,axiom,
    ! [X,Y,Z,U,V,W] :
      ( ( product(X,Y,U)
        & product(Y,Z,V)
        & product(X,V,W) )
     => product(U,Z,W) ) ).

%--------------------------------------------------------------------------

```

### ./GRP003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory
% Axioms   : Group theory axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   5 unt;   0 nHn;   3 RR)
%            Number of literals    :   16 (   1 equ;   8 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :   22 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
%          : These axioms are used in [Wos88] p.184.
%--------------------------------------------------------------------------
cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(right_identity,axiom,
    product(X,identity,X) ).

cnf(left_inverse,axiom,
    product(inverse(X),X,identity) ).

cnf(right_inverse,axiom,
    product(X,inverse(X),identity) ).

%----This axiom is called closure or totality in some axiomatisations
cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | Z = W ) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

%--------------------------------------------------------------------------

```

### ./GRP003-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP003-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory (Subgroups)
% Axioms   : Subgroup axioms for the GRP003 group theory axioms
% Version  : [MOW76] axioms : Reduced > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    2 (   0 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   0 equ;   4 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : 

% Comments : Requires GRP003-0.ax
%          : The dependent axiom, that identity is in every subgroup, is
%            omitted.
%          : These axioms are used in [Wos88] p.187, but with the dependent
%            axiom.
%--------------------------------------------------------------------------
cnf(closure_of_inverse,axiom,
    ( ~ subgroup_member(X)
    | subgroup_member(inverse(X)) ) ).

cnf(closure_of_product,axiom,
    ( ~ subgroup_member(A)
    | ~ subgroup_member(B)
    | ~ product(A,B,C)
    | subgroup_member(C) ) ).

%--------------------------------------------------------------------------

```

### ./GRP003-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP003-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory (Subgroups)
% Axioms   : Subgroup axioms for the GRP003 group theory axioms
% Version  : [Wos65] axioms.
% English  :

% Refs     : [Wos65] Wos (1965), Unpublished Note
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   0 unt;   0 nHn;   1 RR)
%            Number of literals    :    4 (   0 equ;   3 neg)
%            Maximal clause size   :    4 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : 

% Comments : Requires GRP003-0.ax
%            The closure_of_product_and_inverse axiom is derived from the
%            two basic subgroup axioms - closure of product and
%            closure_of_inverse - by resolution.
%--------------------------------------------------------------------------
cnf(closure_of_product_and_inverse,axiom,
    ( ~ subgroup_member(A)
    | ~ subgroup_member(B)
    | ~ product(A,inverse(B),C)
    | subgroup_member(C) ) ).

%--------------------------------------------------------------------------

```

### ./GRP004+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP004+0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory
% Axioms   : Group theory (equality) axioms
% Version  : [MOW76] (equality) axioms :
%            Reduced > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   3 unt;   0 def)
%            Number of atoms       :    3 (   3 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   3 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    5 (   5   !;   0   ?)
% SPC      : 

% Comments : Reverse engineered from GRP004-0.ax.
%--------------------------------------------------------------------------
%----There exists an identity element
fof(left_identity,axiom,
    ! [X] : multiply(identity,X) = X ).

%----For any x in the group, there exists an element y such that x*y = y*x
%----= identity.
fof(left_inverse,axiom,
    ! [X] : multiply(inverse(X),X) = identity ).

%----The operation '*' is associative
fof(associativity,axiom,
    ! [X,Y,Z] : multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./GRP004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP004-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory
% Axioms   : Group theory (equality) axioms
% Version  : [MOW76] (equality) axioms :
%            Reduced > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   0 RR)
%            Number of literals    :    3 (   3 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : 

% Comments : [MOW76] also contains redundant right_identity and
%            right_inverse axioms.
%          : These axioms are also used in [Wos88] p.186, also with
%            right_identity and right_inverse.
%--------------------------------------------------------------------------
%----For any x and y in the group x*y is also in the group. No clause
%----is needed here since this is an instance of reflexivity

%----There exists an identity element
cnf(left_identity,axiom,
    multiply(identity,X) = X ).

%----For any x in the group, there exists an element y such that x*y = y*x
%----= identity.
cnf(left_inverse,axiom,
    multiply(inverse(X),X) = identity ).

%----The operation '*' is associative
cnf(associativity,axiom,
    multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./GRP004-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP004-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory (Subgroups)
% Axioms   : Subgroup (equality) axioms
% Version  : [MOW76] (equality) axioms :
%            Reduced > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    2 (   0 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   1 equ;   4 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 1-2 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : 

% Comments : Requires GRP004-0.ax
%          : The redundant axiom that states that the identity element is in
%            the subgroup, present in the [MOW76] presentation, is omitted
%            here.
%--------------------------------------------------------------------------
cnf(closure_of_inverse,axiom,
    ( ~ subgroup_member(X)
    | subgroup_member(inverse(X)) ) ).

cnf(closure_of_multiply,axiom,
    ( ~ subgroup_member(X)
    | ~ subgroup_member(Y)
    | multiply(X,Y) != Z
    | subgroup_member(Z) ) ).

%--------------------------------------------------------------------------

```

### ./GRP004-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP004-2 : TPTP v8.2.0. Bugfixed v1.2.0.
% Domain   : Group Theory (Lattice Ordered)
% Axioms   : Lattice ordered group (equality) axioms
% Version  : [Fuc94] (equality) axioms.
% English  :

% Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri
%          : [Sch95] Schulz (1995), Explanation Based Learning for Distribu
% Source   : [Sch95]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   12 (  12 unt;   0 nHn;   0 RR)
%            Number of literals    :   12 (  12 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 2-2 aty)
%            Number of variables   :   28 (   2 sgn)
% SPC      : 

% Comments : Requires GRP004-0.ax
%--------------------------------------------------------------------------
%----Specification of the least upper bound and greatest lower bound
cnf(symmetry_of_glb,axiom,
    greatest_lower_bound(X,Y) = greatest_lower_bound(Y,X) ).

cnf(symmetry_of_lub,axiom,
    least_upper_bound(X,Y) = least_upper_bound(Y,X) ).

cnf(associativity_of_glb,axiom,
    greatest_lower_bound(X,greatest_lower_bound(Y,Z)) = greatest_lower_bound(greatest_lower_bound(X,Y),Z) ).

cnf(associativity_of_lub,axiom,
    least_upper_bound(X,least_upper_bound(Y,Z)) = least_upper_bound(least_upper_bound(X,Y),Z) ).

cnf(idempotence_of_lub,axiom,
    least_upper_bound(X,X) = X ).

cnf(idempotence_of_gld,axiom,
    greatest_lower_bound(X,X) = X ).

cnf(lub_absorbtion,axiom,
    least_upper_bound(X,greatest_lower_bound(X,Y)) = X ).

cnf(glb_absorbtion,axiom,
    greatest_lower_bound(X,least_upper_bound(X,Y)) = X ).

%----Monotony of multiply
cnf(monotony_lub1,axiom,
    multiply(X,least_upper_bound(Y,Z)) = least_upper_bound(multiply(X,Y),multiply(X,Z)) ).

cnf(monotony_glb1,axiom,
    multiply(X,greatest_lower_bound(Y,Z)) = greatest_lower_bound(multiply(X,Y),multiply(X,Z)) ).

cnf(monotony_lub2,axiom,
    multiply(least_upper_bound(Y,Z),X) = least_upper_bound(multiply(Y,X),multiply(Z,X)) ).

cnf(monotony_glb2,axiom,
    multiply(greatest_lower_bound(Y,Z),X) = greatest_lower_bound(multiply(Y,X),multiply(Z,X)) ).

%--------------------------------------------------------------------------

```

### ./GRP005-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP005-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group Theory
% Axioms   : Group theory axioms
% Version  : [Ver92] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [Ver92] Veroff (1992), Email to G. Sutcliffe
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : [Ver92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    7 (   3 unt;   0 nHn;   4 RR)
%            Number of literals    :   17 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :   24 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
%          : Note that the axioms of equality are dependent on this set!
%          : These axioms are used in [Wos88] p.185.
%--------------------------------------------------------------------------
cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(left_inverse,axiom,
    product(inverse(X),X,identity) ).

%----This axiom is called closure or totality in some axiomatisations
cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | equalish(Z,W) ) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

cnf(product_substitution3,axiom,
    ( ~ equalish(X,Y)
    | ~ product(W,Z,X)
    | product(W,Z,Y) ) ).

%--------------------------------------------------------------------------

```

### ./GRP006-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP006-0 : TPTP v8.2.0. Bugfixed v1.2.1.
% Domain   : Group Theory (Named groups)
% Axioms   : Group theory (Named groups) axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   5 unt;   0 nHn;   6 RR)
%            Number of literals    :   24 (   1 equ;  13 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-4 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-3 aty)
%            Number of variables   :   36 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
% Bugfixes : v1.2.1 - Clause associativity1 fixed. This is a typo in
%            [MOW76], and is wrong in [ANL].
%--------------------------------------------------------------------------
cnf(identity_in_group,axiom,
    group_member(identity_for(Xg),Xg) ).

cnf(left_identity,axiom,
    product(Xg,identity_for(Xg),X,X) ).

cnf(right_identity,axiom,
    product(Xg,X,identity_for(Xg),X) ).

cnf(inverse_in_group,axiom,
    ( ~ group_member(X,Xg)
    | group_member(inverse(Xg,X),Xg) ) ).

cnf(left_inverse,axiom,
    product(Xg,inverse(Xg,X),X,identity_for(Xg)) ).

cnf(right_inverse,axiom,
    product(Xg,X,inverse(Xg,X),identity_for(Xg)) ).

%----These axioms are called closure or totality in some axiomatisations
cnf(total_function1_1,axiom,
    ( ~ group_member(X,Xg)
    | ~ group_member(Y,Xg)
    | product(Xg,X,Y,multiply(Xg,X,Y)) ) ).

cnf(total_function1_2,axiom,
    ( ~ group_member(X,Xg)
    | ~ group_member(Y,Xg)
    | group_member(multiply(Xg,X,Y),Xg) ) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(Xg,X,Y,Z)
    | ~ product(Xg,X,Y,W)
    | W = Z ) ).

cnf(associativity1,axiom,
    ( ~ product(Xg,X,Y,Xy)
    | ~ product(Xg,Y,Z,Yz)
    | ~ product(Xg,Xy,Z,Xyz)
    | product(Xg,X,Yz,Xyz) ) ).

cnf(associativity2,axiom,
    ( ~ product(Xg,X,Y,Xy)
    | ~ product(Xg,Y,Z,Yz)
    | ~ product(Xg,X,Yz,Xyz)
    | product(Xg,Xy,Z,Xyz) ) ).

%--------------------------------------------------------------------------

```

### ./GRP007+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : GRP007+0 : TPTP v8.2.0. Released v2.0.0.
% Domain   : Group Theory (Named Semigroups)
% Axioms   : Group theory (Named Semigroups) axioms
% Version  : [Gol93] axioms.
% English  :

% Refs     : [Gol93] Goller (1993), Anwendung des Theorembeweisers SETHEO a
% Source   : [Gol93]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :    7 (   1 equ)
%            Maximal formula atoms :    4 (   3 avg)
%            Number of connectives :    5 (   0   ~;   0   |;   3   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   7 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :    7 (   7   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(total_function,axiom,
    ! [G,X,Y] :
      ( ( group_member(X,G)
        & group_member(Y,G) )
     => group_member(multiply(G,X,Y),G) ) ).

fof(associativity,axiom,
    ! [G,X,Y,Z] :
      ( ( group_member(X,G)
        & group_member(Y,G)
        & group_member(Z,G) )
     => multiply(G,multiply(G,X,Y),Z) = multiply(G,X,multiply(G,Y,Z)) ) ).

%------------------------------------------------------------------------------

```

### ./GRP008-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP008-0 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Group Theory (Semigroups)
% Axioms   : Semigroups axioms
% Version  : [MP96] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   1 unt;   0 nHn;   0 RR)
%            Number of literals    :    1 (   1 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Associativity:
cnf(associativity_of_multiply,axiom,
    multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./GRP008-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : GRP008-1 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Group Theory (Cancellative semigroups)
% Axioms   : Cancellative semigroups axioms
% Version  : [MP96] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    2 (   0 unt;   0 nHn;   2 RR)
%            Number of literals    :    4 (   4 equ;   2 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :    6 (   0 sgn)
% SPC      : 

% Comments : Requires GRP008-0.ax
%--------------------------------------------------------------------------
%----Left and right cancellation:
cnf(right_cancellation,axiom,
    ( multiply(A,B) != multiply(C,B)
    | A = C ) ).

cnf(left_cancellation,axiom,
    ( multiply(A,B) != multiply(A,C)
    | B = C ) ).

%--------------------------------------------------------------------------

```

## Homological Algebra

### ./HAL001+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HAL001+0 : TPTP v8.2.0. Released v2.6.0.
% Domain   : Homological Algebra
% Axioms   : Standard homological algebra axioms
% Version  : [TPTP] axioms.
% English  :

% Refs     : [Wei94] Weibel (1994), An Introduction to Homological Algebra
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   13 (   0 unt;   0 def)
%            Number of atoms       :   66 (  16 equ)
%            Maximal formula atoms :    7 (   5 avg)
%            Number of connectives :   53 (   0   ~;   0   |;  30   &)
%                                         (   2 <=>;  21  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   16 (  10 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    7 (   6 usr;   0 prp; 1-4 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-3 aty)
%            Number of variables   :   69 (  65   !;   4   ?)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
fof(morphism,axiom,
    ! [Morphism,Dom,Cod] :
      ( morphism(Morphism,Dom,Cod)
     => ( ! [El] :
            ( element(El,Dom)
           => element(apply(Morphism,El),Cod) )
        & apply(Morphism,zero(Dom)) = zero(Cod) ) ) ).

fof(injection_properties,axiom,
    ! [Morphism,Dom,Cod] :
      ( ( injection(Morphism)
        & morphism(Morphism,Dom,Cod) )
     => ! [El1,El2] :
          ( ( element(El1,Dom)
            & element(El2,Dom)
            & apply(Morphism,El1) = apply(Morphism,El2) )
         => El1 = El2 ) ) ).

fof(properties_for_injection,axiom,
    ! [Morphism,Dom,Cod] :
      ( ( morphism(Morphism,Dom,Cod)
        & ! [El1,El2] :
            ( ( element(El1,Dom)
              & element(El2,Dom)
              & apply(Morphism,El1) = apply(Morphism,El2) )
           => El1 = El2 ) )
     => injection(Morphism) ) ).

%----Sasha's weird injection axioms
% input_formula(injection_properties,axiom, (
%     ! [Morphism,Dom,Cod] :
%       ( ( injection(Morphism)
%         & morphism(Morphism,Dom,Cod) )
%      => ! [El] :
%           ( ( element(El,Dom)
%             & equal(apply(Morphism,El),zero(Cod)) )
%          => equal(El,zero(Dom)) ) )  )).
%
% input_formula(properties_for_injection,axiom, (
%     ! [Morphism,Dom,Cod] :
%       ( ( morphism(Morphism,Dom,Cod)
%         & ! [El] :
%             ( ( element(El,Dom)
%               & equal(apply(Morphism,El),zero(Cod)) )
%            => equal(El,zero(Dom)) ) )
%      => injection(Morphism) )  )).

fof(surjection_properties,axiom,
    ! [Morphism,Dom,Cod] :
      ( ( surjection(Morphism)
        & morphism(Morphism,Dom,Cod) )
     => ! [ElCod] :
          ( element(ElCod,Cod)
         => ? [ElDom] :
              ( element(ElDom,Dom)
              & apply(Morphism,ElDom) = ElCod ) ) ) ).

fof(properties_for_surjection,axiom,
    ! [Morphism,Dom,Cod] :
      ( ( morphism(Morphism,Dom,Cod)
        & ! [ElCod] :
            ( element(ElCod,Cod)
           => ? [ElDom] :
                ( element(ElDom,Dom)
                & apply(Morphism,ElDom) = ElCod ) ) )
     => surjection(Morphism) ) ).

fof(exact_properties,axiom,
    ! [Morphism1,Morphism2,Dom,CodDom,Cod] :
      ( ( exact(Morphism1,Morphism2)
        & morphism(Morphism1,Dom,CodDom)
        & morphism(Morphism2,CodDom,Cod) )
     => ! [ElCodDom] :
          ( ( element(ElCodDom,CodDom)
            & apply(Morphism2,ElCodDom) = zero(Cod) )
        <=> ? [ElDom] :
              ( element(ElDom,Dom)
              & apply(Morphism1,ElDom) = ElCodDom ) ) ) ).

fof(properties_for_exact,axiom,
    ! [Morphism1,Morphism2,Dom,CodDom,Cod] :
      ( ( morphism(Morphism1,Dom,CodDom)
        & morphism(Morphism2,CodDom,Cod)
        & ! [ElCodDom] :
            ( ( element(ElCodDom,CodDom)
              & apply(Morphism2,ElCodDom) = zero(Cod) )
          <=> ? [ElDom] :
                ( element(ElDom,Dom)
                & apply(Morphism1,ElDom) = ElCodDom ) ) )
     => exact(Morphism1,Morphism2) ) ).

fof(commute_properties,axiom,
    ! [M1,M2,M3,M4,Dom,DomCod1,DomCod2,Cod] :
      ( ( commute(M1,M2,M3,M4)
        & morphism(M1,Dom,DomCod1)
        & morphism(M2,DomCod1,Cod)
        & morphism(M3,Dom,DomCod2)
        & morphism(M4,DomCod2,Cod) )
     => ! [ElDom] :
          ( element(ElDom,Dom)
         => apply(M2,apply(M1,ElDom)) = apply(M4,apply(M3,ElDom)) ) ) ).

fof(properties_for_commute,axiom,
    ! [M1,M2,M3,M4,Dom,DomCod1,DomCod2,Cod] :
      ( ( morphism(M1,Dom,DomCod1)
        & morphism(M2,DomCod1,Cod)
        & morphism(M3,Dom,DomCod2)
        & morphism(M4,DomCod2,Cod)
        & ! [ElDom] :
            ( element(ElDom,Dom)
           => apply(M2,apply(M1,ElDom)) = apply(M4,apply(M3,ElDom)) ) )
     => commute(M1,M2,M3,M4) ) ).

fof(subtract_in_domain,axiom,
    ! [Dom,El1,El2] :
      ( ( element(El1,Dom)
        & element(El2,Dom) )
     => element(subtract(Dom,El1,El2),Dom) ) ).

fof(subtract_to_0,axiom,
    ! [Dom,El] :
      ( element(El,Dom)
     => subtract(Dom,El,El) = zero(Dom) ) ).

fof(subtract_cancellation,axiom,
    ! [Dom,El1,El2] :
      ( ( element(El1,Dom)
        & element(El2,Dom) )
     => subtract(Dom,El1,subtract(Dom,El1,El2)) = El2 ) ).

fof(subtract_distribution,axiom,
    ! [Morphism,Dom,Cod] :
      ( morphism(Morphism,Dom,Cod)
     => ! [El1,El2] :
          ( ( element(El1,Dom)
            & element(El2,Dom) )
         => apply(Morphism,subtract(Dom,El1,El2)) = subtract(Cod,apply(Morphism,El1),apply(Morphism,El2)) ) ) ).

%--------------------------------------------------------------------------

```

## Henkin Models

### ./HEN001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HEN001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Henkin Models
% Axioms   : Henkin model axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    9 (   3 unt;   0 nHn;   6 RR)
%            Number of literals    :   21 (   2 equ;  12 neg)
%            Maximal clause size   :    6 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :   25 (   3 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----A0: definition of less than or equal to
cnf(quotient_less_equal,axiom,
    ( ~ less_equal(X,Y)
    | quotient(X,Y,zero) ) ).

cnf(less_equal_quotient,axiom,
    ( ~ quotient(X,Y,zero)
    | less_equal(X,Y) ) ).

%----A1: x/y <= x
cnf(divisor_existence,axiom,
    ( ~ quotient(X,Y,Z)
    | less_equal(Z,X) ) ).

%----A2: (x/z) / (y/z) <= (x/y) / z
cnf(quotient_property,axiom,
    ( ~ quotient(X,Y,V1)
    | ~ quotient(Y,Z,V2)
    | ~ quotient(X,Z,V3)
    | ~ quotient(V3,V2,V4)
    | ~ quotient(V1,Z,V5)
    | less_equal(V4,V5) ) ).

%----A3: 0 <= x
cnf(zero_is_smallest,axiom,
    less_equal(zero,X) ).

%----A4: x <= y and y <= x implies that x = y
cnf(less_equal_and_equal,axiom,
    ( ~ less_equal(X,Y)
    | ~ less_equal(Y,X)
    | X = Y ) ).

%----A5: x <= identity (Thus an implicative model with unit 1)
cnf(identity_is_largest,axiom,
    less_equal(X,identity) ).

%----closure of '/'
cnf(closure,axiom,
    quotient(X,Y,divide(X,Y)) ).

%----'/' is well defined
cnf(well_defined,axiom,
    ( ~ quotient(X,Y,Z)
    | ~ quotient(X,Y,W)
    | Z = W ) ).

%--------------------------------------------------------------------------

```

### ./HEN002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HEN002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Henkin Models
% Axioms   : Henkin model axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    7 (   4 unt;   0 nHn;   3 RR)
%            Number of literals    :   11 (   3 equ;   4 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :   13 (   3 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----A0: Definition of less_equal
cnf(quotient_less_equal1,axiom,
    ( ~ less_equal(X,Y)
    | divide(X,Y) = zero ) ).

cnf(quotient_less_equal2,axiom,
    ( divide(X,Y) != zero
    | less_equal(X,Y) ) ).

%----A1: x/y <= x
cnf(quotient_smaller_than_numerator,axiom,
    less_equal(divide(X,Y),X) ).

%----A2: (x/z) / (y/z) <= (x/y) / z
cnf(quotient_property,axiom,
    less_equal(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z)) ).

%----A3: 0<=x
cnf(zero_is_smallest,axiom,
    less_equal(zero,X) ).

%----A4: x <= y and y <= x implies that x = y
cnf(less_equal_and_equal,axiom,
    ( ~ less_equal(X,Y)
    | ~ less_equal(Y,X)
    | X = Y ) ).

%----A5: x <= identity (Thus an implicative model with unit )
cnf(identity_is_largest,axiom,
    less_equal(X,identity) ).

%----Implicit in equality formulation: '/' is well defined
%--------------------------------------------------------------------------

```

### ./HEN003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HEN003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Henkin Models
% Axioms   : Henkin model (equality) axioms
% Version  : [MOW76] (equality) axioms :
%            Reduced > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   1 RR)
%            Number of literals    :    7 (   7 equ;   2 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :    9 (   3 sgn)
% SPC      : 

% Comments : less_equal replaced by divides
%--------------------------------------------------------------------------
%----A0: Definition of less_equal, used to replace all occurrences
%----of less_equal(x,y)
%----    --less_equal(x,y) | (divide(x,y) = zero).
%----    (divide(x,y) != zero) | ++less_equal(x,y).

%----A1: x/y <= x
cnf(quotient_smaller_than_numerator,axiom,
    divide(divide(X,Y),X) = zero ).

%----A2: (x/z) / (y/z) <= (x/y) / z
cnf(quotient_property,axiom,
    divide(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z)) = zero ).

%----A3: 0<=x  NOTE: this axiom is dependant
cnf(zero_is_smallest,axiom,
    divide(zero,X) = zero ).

%----A4: x <= y and y <= x implies that x = y
cnf(divide_and_equal,axiom,
    ( divide(X,Y) != zero
    | divide(Y,X) != zero
    | X = Y ) ).

%----A5: x <= 1 (Thus an implicative model with unit )
cnf(identity_is_largest,axiom,
    divide(X,identity) = zero ).

%----Implicit in equality formulation: '/' is well defined

%--------------------------------------------------------------------------

```

## Hardware Creation

### ./HWC001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWC001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Hardware Creation
% Axioms   : Definitions of AND, OR and NOT
% Version  : [WO+92] axioms.
%            Axiom formulation : Ground axioms.
% English  :

% Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   10 (  10 unt;   0 nHn;  10 RR)
%            Number of literals    :   10 (  10 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(and_definition1,axiom,
    and(n0,n0) = n0 ).

cnf(and_definition2,axiom,
    and(n0,n1) = n0 ).

cnf(and_definition3,axiom,
    and(n1,n0) = n0 ).

cnf(and_definition4,axiom,
    and(n1,n1) = n1 ).

cnf(or_definition1,axiom,
    or(n0,n0) = n0 ).

cnf(or_definition2,axiom,
    or(n0,n1) = n1 ).

cnf(or_definition3,axiom,
    or(n1,n0) = n1 ).

cnf(or_definition4,axiom,
    or(n1,n1) = n1 ).

cnf(not_definition1,axiom,
    not(n0) = n1 ).

cnf(not_definition2,axiom,
    not(n1) = n0 ).

%--------------------------------------------------------------------------

```

### ./HWC002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWC002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Hardware Creation
% Axioms   : Definitions of AND, OR and NOT
% Version  : [WO+92] axioms.
%            Axiom formulation : Non-ground axioms.
% English  :

% Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   6 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    4 (   2 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(and_definition1,axiom,
    and(X,n0) = n0 ).

cnf(and_definition2,axiom,
    and(X,n1) = X ).

cnf(or_definition1,axiom,
    or(X,n0) = X ).

cnf(or_definition2,axiom,
    or(X,n1) = n1 ).

cnf(not_definition1,axiom,
    not(n0) = n1 ).

cnf(not_definition2,axiom,
    not(n1) = n0 ).

%--------------------------------------------------------------------------

```

## Hardware Verification

### ./HWV001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV001-0 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Connections, faults, and gates.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   21 (   2 unt;   3 nHn;  21 RR)
%            Number of literals    :   76 (   0 equ;  55 neg)
%            Maximal clause size   :    5 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 2-2 aty)
%            Number of functors    :   10 (  10 usr;   8 con; 0-2 aty)
%            Number of variables   :   28 (   3 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Properties of connections and values
cnf(value_propagation1,axiom,
    ( ~ connection(P1,P2)
    | ~ value(P1,V)
    | value(P2,V) ) ).

cnf(value_propagation2,axiom,
    ( ~ connection(P1,P2)
    | ~ value(P2,V)
    | value(P1,V) ) ).

cnf(unique_value,axiom,
    ( ~ value(P,V1)
    | ~ value(P,V2)
    | equal_value(V1,V2) ) ).

cnf(equal_value1,axiom,
    ~ equal_value(n0,n1) ).

cnf(equal_value2,axiom,
    ~ equal_value(n1,n0) ).

%----Fault model
cnf(not_ok_and_abnormal,axiom,
    ( ~ mode(K,ok)
    | ~ mode(K,abnormal) ) ).

cnf(ok_or_abnormal,axiom,
    ( ~ type(K,Any)
    | mode(K,ok)
    | mode(K,abnormal) ) ).

%----AND gate
cnf(and_0x_0,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,and)
    | ~ value(in(Any,K),n0)
    | value(out(n1,K),n0) ) ).

cnf(and_11_1,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,and)
    | ~ value(in(n1,K),n1)
    | ~ value(in(n2,K),n1)
    | value(out(n1,K),n1) ) ).

cnf(and_0_00,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,and)
    | ~ value(out(n1,K),n0)
    | value(in(n1,K),n0)
    | value(in(n2,K),n0) ) ).

cnf(and_1_1x,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,and)
    | ~ value(out(n1,K),n1)
    | value(in(n1,K),n1) ) ).

cnf(and_1_x1,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,and)
    | ~ value(out(n1,K),n1)
    | value(in(n2,K),n1) ) ).

%----OR gate
cnf(or_1x_1,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,or)
    | ~ value(in(Any,K),n1)
    | value(out(n1,K),n1) ) ).

cnf(or_00_0,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,or)
    | ~ value(in(n1,K),n0)
    | ~ value(in(n2,K),n0)
    | value(out(n1,K),n0) ) ).

cnf(or_1_11,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,or)
    | ~ value(out(n1,K),n1)
    | value(in(n1,K),n1)
    | value(in(n2,K),n1) ) ).

cnf(or_0_0x,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,or)
    | ~ value(out(n1,K),n0)
    | value(in(n1,K),n0) ) ).

cnf(or_0_01,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,or)
    | ~ value(out(n1,K),n0)
    | value(in(n2,K),n0) ) ).

%----NOT gate
cnf(not_0_1_fw,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,not)
    | ~ value(in(n1,K),n0)
    | value(out(n1,K),n1) ) ).

cnf(not_1_0_fw,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,not)
    | ~ value(in(n1,K),n1)
    | value(out(n1,K),n0) ) ).

cnf(not_0_1_bw,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,not)
    | ~ value(out(n1,K),n0)
    | value(in(n1,K),n1) ) ).

cnf(not_1_0_bw,axiom,
    ( ~ mode(K,ok)
    | ~ type(K,not)
    | ~ value(out(n1,K),n1)
    | value(in(n1,K),n0) ) ).

%--------------------------------------------------------------------------

```

### ./HWV001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV001-1 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Half-adder.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   13 (   0 unt;   0 nHn;  13 RR)
%            Number of literals    :   26 (   0 equ;  13 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :   14 (  14 usr;   8 con; 0-2 aty)
%            Number of variables   :   13 (   0 sgn)
% SPC      : 

% Comments : Requires HWV001-0.ax
%--------------------------------------------------------------------------
%----Composition of halfadder
cnf(halfadder_and1,axiom,
    ( ~ type(X,halfadder)
    | type(and1(X),and) ) ).

cnf(halfadder_and2,axiom,
    ( ~ type(X,halfadder)
    | type(and2(X),and) ) ).

cnf(halfadder_not1,axiom,
    ( ~ type(X,halfadder)
    | type(not1(X),not) ) ).

cnf(halfadder_or1,axiom,
    ( ~ type(X,halfadder)
    | type(or1(X),or) ) ).

%----Connections of halfadder
cnf(halfadder_connection_in1_in1or1,axiom,
    ( ~ type(X,halfadder)
    | connection(in(n1,X),in(n1,or1(X))) ) ).

cnf(halfadder_connection_in2_in2or1,axiom,
    ( ~ type(X,halfadder)
    | connection(in(n2,X),in(n2,or1(X))) ) ).

cnf(halfadder_connection_in1_in1and2,axiom,
    ( ~ type(X,halfadder)
    | connection(in(n1,X),in(n1,and2(X))) ) ).

cnf(halfadder_connection_in2_in2and2,axiom,
    ( ~ type(X,halfadder)
    | connection(in(n2,X),in(n2,and2(X))) ) ).

cnf(halfadder_connection_outs_out1and1,axiom,
    ( ~ type(X,halfadder)
    | connection(out(s,X),out(n1,and1(X))) ) ).

cnf(halfadder_connection_outc_out1and2,axiom,
    ( ~ type(X,halfadder)
    | connection(out(c,X),out(n1,and2(X))) ) ).

cnf(halfadder_connection_out1or1_in1_and1,axiom,
    ( ~ type(X,halfadder)
    | connection(out(n1,or1(X)),in(n1,and1(X))) ) ).

cnf(halfadder_connection_out1and2_in1not1,axiom,
    ( ~ type(X,halfadder)
    | connection(out(n1,and2(X)),in(n1,not1(X))) ) ).

cnf(halfadder_connection_out1not1_in2and1,axiom,
    ( ~ type(X,halfadder)
    | connection(out(n1,not1(X)),in(n2,and1(X))) ) ).

%--------------------------------------------------------------------------

```

### ./HWV001-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV001-2 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Full-adder.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   0 unt;   0 nHn;  11 RR)
%            Number of literals    :   22 (   0 equ;  11 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :   12 (  12 usr;   7 con; 0-2 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : 

% Comments : Requires HWV001-0.ax HWV001-1.ax
%--------------------------------------------------------------------------
%----Composition of fulladder
cnf(fulladder_halfadder1,axiom,
    ( ~ type(X,fulladder)
    | type(h1(X),halfadder) ) ).

cnf(fulladder_halfadder2,axiom,
    ( ~ type(X,fulladder)
    | type(h2(X),halfadder) ) ).

cnf(fulladder_or1,axiom,
    ( ~ type(X,fulladder)
    | type(or1(X),or) ) ).

%----Connections of fulladder
cnf(fulladder_connection_outsh1_in2h2,axiom,
    ( ~ type(X,fulladder)
    | connection(out(s,h1(X)),in(n2,h2(X))) ) ).

cnf(fulladder_connection_outch1_in2or1,axiom,
    ( ~ type(X,fulladder)
    | connection(out(c,h1(X)),in(n2,or1(X))) ) ).

cnf(fulladder_connection_outch2_in1or1,axiom,
    ( ~ type(X,fulladder)
    | connection(out(c,h2(X)),in(n1,or1(X))) ) ).

cnf(fulladder_connection_in1_in1h2,axiom,
    ( ~ type(X,fulladder)
    | connection(in(n1,X),in(n1,h2(X))) ) ).

cnf(fulladder_connection_in2_in1h1,axiom,
    ( ~ type(X,fulladder)
    | connection(in(n2,X),in(n1,h1(X))) ) ).

cnf(fulladder_connection_inc_in2h1,axiom,
    ( ~ type(X,fulladder)
    | connection(in(c,X),in(n2,h1(X))) ) ).

cnf(fulladder_connection_outs_outsh2,axiom,
    ( ~ type(X,fulladder)
    | connection(out(s,X),out(s,h2(X))) ) ).

cnf(fulladder_connection_outc_out1or1,axiom,
    ( ~ type(X,fulladder)
    | connection(out(c,X),out(n1,or1(X))) ) ).

%--------------------------------------------------------------------------

```

### ./HWV002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV002-0 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Connections, faults, and gates.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   27 (   0 unt;   5 nHn;  27 RR)
%            Number of literals    :   81 (   0 equ;  53 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-1 aty)
%            Number of variables   :   31 (   0 sgn)
% SPC      : 

% Comments :
% Bugfixes : v2.7.0 - Fixed clause not_ok_or_abnormal
%--------------------------------------------------------------------------
%----Properties of connections and values
cnf(value_propagation_zero1,axiom,
    ( ~ connection(P1,P2)
    | ~ zero(P1)
    | zero(P2) ) ).

cnf(value_propagation_one1,axiom,
    ( ~ connection(P1,P2)
    | ~ one(P1)
    | one(P2) ) ).

cnf(value_propagation_zero2,axiom,
    ( ~ connection(P1,P2)
    | ~ zero(P2)
    | zero(P1) ) ).

cnf(value_propagation_one2,axiom,
    ( ~ connection(P1,P2)
    | ~ one(P2)
    | one(P1) ) ).

cnf(unique_value,axiom,
    ( ~ zero(P)
    | ~ one(P) ) ).

%----AND gate
cnf(and_0x_0,axiom,
    ( ~ and_ok(K)
    | ~ zero(in1(K))
    | zero(out1(K)) ) ).

cnf(and_x0_0,axiom,
    ( ~ and_ok(K)
    | ~ zero(in2(K))
    | zero(out1(K)) ) ).

cnf(and_11_1,axiom,
    ( ~ and_ok(K)
    | ~ one(in1(K))
    | ~ one(in2(K))
    | one(out1(K)) ) ).

cnf(and_0_00,axiom,
    ( ~ and_ok(K)
    | ~ zero(out1(K))
    | zero(in1(K))
    | zero(in2(K)) ) ).

cnf(and_1_1x,axiom,
    ( ~ and_ok(K)
    | ~ one(out1(K))
    | one(in1(K)) ) ).

cnf(and_1_x1,axiom,
    ( ~ and_ok(K)
    | ~ one(out1(K))
    | one(in2(K)) ) ).

%----Fault model for AND
cnf(not_and_ok_and_abnormal,axiom,
    ( ~ and_ok(K)
    | ~ abnormal(K) ) ).

cnf(and_ok_or_abnormal,axiom,
    ( ~ logic_and(K)
    | and_ok(K)
    | abnormal(K) ) ).

%----OR gate
cnf(or_1x_1,axiom,
    ( ~ or_ok(K)
    | ~ one(in1(K))
    | one(out1(K)) ) ).

cnf(or_x1_1,axiom,
    ( ~ or_ok(K)
    | ~ one(in2(K))
    | one(out1(K)) ) ).

cnf(or_00_0,axiom,
    ( ~ or_ok(K)
    | ~ zero(in1(K))
    | ~ zero(in2(K))
    | zero(out1(K)) ) ).

cnf(or_1_11,axiom,
    ( ~ or_ok(K)
    | ~ one(out1(K))
    | one(in1(K))
    | one(in2(K)) ) ).

cnf(or_0_0x,axiom,
    ( ~ or_ok(K)
    | ~ zero(out1(K))
    | zero(in1(K)) ) ).

cnf(or_0_01,axiom,
    ( ~ or_ok(K)
    | ~ zero(out1(K))
    | zero(in2(K)) ) ).

%----Fault model for OR
cnf(not_or_ok_and_abnormal,axiom,
    ( ~ or_ok(K)
    | ~ abnormal(K) ) ).

cnf(or_ok_or_abnormal,axiom,
    ( ~ logic_or(K)
    | or_ok(K)
    | abnormal(K) ) ).

%----NOT gate
cnf(not_0_1_fw,axiom,
    ( ~ not_ok(K)
    | ~ zero(in1(K))
    | one(out1(K)) ) ).

cnf(not_1_0_fw,axiom,
    ( ~ not_ok(K)
    | ~ one(in1(K))
    | zero(out1(K)) ) ).

cnf(not_0_1_bw,axiom,
    ( ~ not_ok(K)
    | ~ zero(out1(K))
    | one(in1(K)) ) ).

cnf(not_1_0_bw,axiom,
    ( ~ not_ok(K)
    | ~ one(out1(K))
    | zero(in1(K)) ) ).

%----Fault model for NOT
cnf(not__not_ok_and_abnormal,axiom,
    ( ~ not_ok(K)
    | ~ abnormal(K) ) ).

cnf(not_ok_or_abnormal,axiom,
    ( ~ logic_not(K)
    | not_ok(K)
    | abnormal(K) ) ).

%--------------------------------------------------------------------------

```

### ./HWV002-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV002-1 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Half-adder.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   13 (   0 unt;   0 nHn;  13 RR)
%            Number of literals    :   26 (   0 equ;  13 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   9 usr;   0 con; 1-1 aty)
%            Number of variables   :   13 (   0 sgn)
% SPC      : 

% Comments : Requires HWV002-0.ax
%--------------------------------------------------------------------------
%----Composition of halfadder
cnf(halfadder_and1,axiom,
    ( ~ halfadder(X)
    | logic_and(and1(X)) ) ).

cnf(halfadder_and2,axiom,
    ( ~ halfadder(X)
    | logic_and(and2(X)) ) ).

cnf(halfadder_not1,axiom,
    ( ~ halfadder(X)
    | logic_not(not1(X)) ) ).

cnf(halfadder_or1,axiom,
    ( ~ halfadder(X)
    | logic_or(or1(X)) ) ).

%----Connections of halfadder
cnf(halfadder_connection_in1_in1or1,axiom,
    ( ~ halfadder(X)
    | connection(in1(X),in1(or1(X))) ) ).

cnf(halfadder_connection_in2_in2or1,axiom,
    ( ~ halfadder(X)
    | connection(in2(X),in2(or1(X))) ) ).

cnf(halfadder_connection_in1_in1and2,axiom,
    ( ~ halfadder(X)
    | connection(in1(X),in1(and2(X))) ) ).

cnf(halfadder_connection_in2_in2and2,axiom,
    ( ~ halfadder(X)
    | connection(in2(X),in2(and2(X))) ) ).

cnf(halfadder_connection_outs_out1and1,axiom,
    ( ~ halfadder(X)
    | connection(outs(X),out1(and1(X))) ) ).

cnf(halfadder_connection_outc_out1and2,axiom,
    ( ~ halfadder(X)
    | connection(outc(X),out1(and2(X))) ) ).

cnf(halfadder_connection_out1or1_in1_and1,axiom,
    ( ~ halfadder(X)
    | connection(out1(or1(X)),in1(and1(X))) ) ).

cnf(halfadder_connection_out1and2_in1not1,axiom,
    ( ~ halfadder(X)
    | connection(out1(and2(X)),in1(not1(X))) ) ).

cnf(halfadder_connection_out1not1_in2and1,axiom,
    ( ~ halfadder(X)
    | connection(out1(not1(X)),in2(and1(X))) ) ).

%--------------------------------------------------------------------------

```

### ./HWV002-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : HWV002-2 : TPTP v8.2.0. Released .0.
% Domain   : Hardware Verification
% Axioms   : Full-adder.
% Version  : [Gei96] axioms.
% English  :

% Refs     : [Gei96] Geisler (1996), Email to G. Sutcliffe
% Source   : [Gei96]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   0 unt;   0 nHn;  11 RR)
%            Number of literals    :   22 (   0 equ;  11 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   9 usr;   0 con; 1-1 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : 

% Comments : Requires HWV002-0.ax HWV002-1.ax
%--------------------------------------------------------------------------
%----Composition of fulladder
cnf(fulladder_halfadder1,axiom,
    ( ~ fulladder(X)
    | halfadder(h1(X)) ) ).

cnf(fulladder_halfadder2,axiom,
    ( ~ fulladder(X)
    | halfadder(h2(X)) ) ).

cnf(fulladder_or1,axiom,
    ( ~ fulladder(X)
    | logic_or(or1(X)) ) ).

%----Connections of fulladder
cnf(fulladder_connection_outsh1_in2h2,axiom,
    ( ~ fulladder(X)
    | connection(outs(h1(X)),in2(h2(X))) ) ).

cnf(fulladder_connection_outch1_in2or1,axiom,
    ( ~ fulladder(X)
    | connection(outc(h1(X)),in2(or1(X))) ) ).

cnf(fulladder_connection_outch2_in1or1,axiom,
    ( ~ fulladder(X)
    | connection(outc(h2(X)),in1(or1(X))) ) ).

cnf(fulladder_connection_in1_in1h2,axiom,
    ( ~ fulladder(X)
    | connection(in1(X),in1(h2(X))) ) ).

cnf(fulladder_connection_in2_in1h1,axiom,
    ( ~ fulladder(X)
    | connection(in2(X),in1(h1(X))) ) ).

cnf(fulladder_connection_inc_in2h1,axiom,
    ( ~ fulladder(X)
    | connection(inc(X),in2(h1(X))) ) ).

cnf(fulladder_connection_outs_outsh2,axiom,
    ( ~ fulladder(X)
    | connection(outs(X),outs(h2(X))) ) ).

cnf(fulladder_connection_outc_out1or1,axiom,
    ( ~ fulladder(X)
    | connection(outc(X),out1(or1(X))) ) ).

%--------------------------------------------------------------------------

```

### ./HWV003-0.ax

Very long 573

### ./HWV004-0.ax

Very long 706

## Kleene Algebra

### ./KLE001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Idempotent semirings
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   12 (  11 unt;   0 def)
%            Number of atoms       :   13 (  12 equ)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   22 (  22   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Additive idempotent monoid
fof(additive_commutativity,axiom,
    ! [A,B] : addition(A,B) = addition(B,A) ).

fof(additive_associativity,axiom,
    ! [C,B,A] : addition(A,addition(B,C)) = addition(addition(A,B),C) ).

fof(additive_identity,axiom,
    ! [A] : addition(A,zero) = A ).

fof(additive_idempotence,axiom,
    ! [A] : addition(A,A) = A ).

%----Multiplicative and commutative monoid
fof(multiplicative_associativity,axiom,
    ! [A,B,C] : multiplication(A,multiplication(B,C)) = multiplication(multiplication(A,B),C) ).

fof(multiplicative_right_identity,axiom,
    ! [A] : multiplication(A,one) = A ).

fof(multiplicative_left_identity,axiom,
    ! [A] : multiplication(one,A) = A ).

%----Distributivity laws
fof(right_distributivity,axiom,
    ! [A,B,C] : multiplication(A,addition(B,C)) = addition(multiplication(A,B),multiplication(A,C)) ).

fof(left_distributivity,axiom,
    ! [A,B,C] : multiplication(addition(A,B),C) = addition(multiplication(A,C),multiplication(B,C)) ).

%----Annihilation
fof(right_annihilation,axiom,
    ! [A] : multiplication(A,zero) = zero ).

fof(left_annihilation,axiom,
    ! [A] : multiplication(zero,A) = zero ).

%----Order
fof(order,axiom,
    ! [A,B] :
      ( leq(A,B)
    <=> addition(A,B) = B ) ).

%------------------------------------------------------------------------------

```

### ./KLE001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+1 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Characterisation of tests by complement predicate
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   0 unt;   0 def)
%            Number of atoms       :   11 (   5 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :    8 (   1   ~;   0   |;   2   &)
%                                         (   3 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    7 (   6   !;   1   ?)
% SPC      : 

% Comments : Requires KLE001+0.ax, KLE002+0.ax or KLE003+0.ax
%          : Combined with KLE001+0 generates Idempotent semirings with tests
%            Combined with KLE002+0 generates Kleene Algebra with tests
%            Combined with KLE003+0 generates Omega Algebra with tests
%------------------------------------------------------------------------------
fof(test_1,axiom,
    ! [X0] :
      ( test(X0)
    <=> ? [X1] : complement(X1,X0) ) ).

fof(test_2,axiom,
    ! [X0,X1] :
      ( complement(X1,X0)
    <=> ( multiplication(X0,X1) = zero
        & multiplication(X1,X0) = zero
        & addition(X0,X1) = one ) ) ).

fof(test_3,axiom,
    ! [X0,X1] :
      ( test(X0)
     => ( c(X0) = X1
      <=> complement(X0,X1) ) ) ).

fof(test_4,axiom,
    ! [X0] :
      ( ~ test(X0)
     => c(X0) = zero ) ).

%------------------------------------------------------------------------------

```

### ./KLE001+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+2 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : de Morgan's laws for tests
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :    6 (   2 equ)
%            Maximal formula atoms :    3 (   3 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   2   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   5 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :    4 (   4   !;   0   ?)
% SPC      : 

% Comments : Requires KLE001+1.ax
%------------------------------------------------------------------------------
fof(test_deMorgan1,axiom,
    ! [X0,X1] :
      ( ( test(X0)
        & test(X1) )
     => c(addition(X0,X1)) = multiplication(c(X0),c(X1)) ) ).

fof(test_deMorgan2,axiom,
    ! [X0,X1] :
      ( ( test(X0)
        & test(X1) )
     => c(multiplication(X0,X1)) = addition(c(X0),c(X1)) ) ).

%------------------------------------------------------------------------------

```

### ./KLE001+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+3 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Universal characterisation of meet
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :   10 (   0 equ)
%            Maximal formula atoms :    6 (   5 avg)
%            Number of connectives :    8 (   0   ~;   0   |;   4   &)
%                                         (   3 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   9 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    8 (   8   !;   0   ?)
% SPC      : 

% Comments : Requires KLE001+0.ax, KLE002+0.ax or KLE003+0.ax
%------------------------------------------------------------------------------
fof(ismeet,axiom,
    ! [X0,X1,X2] :
      ( ismeet(X2,X0,X1)
    <=> ( leq(X2,X0)
        & leq(X2,X1)
        & ! [X3] :
            ( ( leq(X3,X0)
              & leq(X3,X1) )
           => leq(X3,X2) ) ) ) ).

fof(ismeetu,axiom,
    ! [X0,X1,X2] :
      ( ismeetu(X2,X0,X1)
    <=> ! [X3] :
          ( ( leq(X3,X0)
            & leq(X3,X1) )
        <=> leq(X3,X2) ) ) ).

%------------------------------------------------------------------------------

```

### ./KLE001+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+4 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Boolean domain, antidomain, codomain, coantidomain
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   8 unt;   0 def)
%            Number of atoms       :    8 (   8 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    3 (   2 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   2 con; 0-2 aty)
%            Number of variables   :   10 (  10   !;   0   ?)
% SPC      : 

% Comments : Requires KLE001+0.ax, KLE002+0.ax or KLE003+0.ax
%          : With KLE001+0 generates Idempotent semirings with domain/codomain
%            With KLE002+0 generates Kleene Algebra with domain domain/codomain
%            With KLE003+0 generates Omega Algebra with domain/codomain
%------------------------------------------------------------------------------
%----Boolean domain axioms (a la Desharnais & Struth)
fof(domain1,axiom,
    ! [X0] : multiplication(antidomain(X0),X0) = zero ).

fof(domain2,axiom,
    ! [X0,X1] : addition(antidomain(multiplication(X0,X1)),antidomain(multiplication(X0,antidomain(antidomain(X1))))) = antidomain(multiplication(X0,antidomain(antidomain(X1)))) ).

fof(domain3,axiom,
    ! [X0] : addition(antidomain(antidomain(X0)),antidomain(X0)) = one ).

fof(domain4,axiom,
    ! [X0] : domain(X0) = antidomain(antidomain(X0)) ).

%----Boolean codomain axioms (a la Desharnais & Struth)
fof(codomain1,axiom,
    ! [X0] : multiplication(X0,coantidomain(X0)) = zero ).

fof(codomain2,axiom,
    ! [X0,X1] : addition(coantidomain(multiplication(X0,X1)),coantidomain(multiplication(coantidomain(coantidomain(X0)),X1))) = coantidomain(multiplication(coantidomain(coantidomain(X0)),X1)) ).

fof(codomain3,axiom,
    ! [X0] : addition(coantidomain(coantidomain(X0)),coantidomain(X0)) = one ).

fof(codomain4,axiom,
    ! [X0] : codomain(X0) = coantidomain(coantidomain(X0)) ).

%------------------------------------------------------------------------------

```

### ./KLE001+5.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+5 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Domain (not Boolean domain!)
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [DS08]  Desharnais & Struth (2008), Modal Semirings Revisited
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   5 unt;   0 def)
%            Number of atoms       :    5 (   5 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    3 (   2 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    6 (   6   !;   0   ?)
% SPC      : 

% Comments : The domain algebra is not necessarily Boolean
%          : Requires KLE001+0.ax, KLE002+0.ax or KLE003+0.ax
%          : Combined with KLE001+0 generates Idempotent semirings with tests
%            Combined with KLE002+0 generates Kleene Algebra with tests
%            Combined with KLE003+0 generates Omega Algebra with tests
%------------------------------------------------------------------------------
%----Domain axioms (a la Desharnais & Struth)
fof(domain1,axiom,
    ! [X0] : addition(X0,multiplication(domain(X0),X0)) = multiplication(domain(X0),X0) ).

fof(domain2,axiom,
    ! [X0,X1] : domain(multiplication(X0,X1)) = domain(multiplication(X0,domain(X1))) ).

fof(domain3,axiom,
    ! [X0] : addition(domain(X0),one) = one ).

fof(domain4,axiom,
    domain(zero) = zero ).

fof(domain5,axiom,
    ! [X0,X1] : domain(addition(X0,X1)) = addition(domain(X0),domain(X1)) ).

%------------------------------------------------------------------------------

```

### ./KLE001+6.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+6 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Modal operators
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [DMS06] Desharnais et al. (2006), Kleene Algebra with Domain
%          : [MS06]  Moeller & Struth (2006), Algebras of Modal Operators a
%          : [DS08]  Desharnais & Struth (2008), Modal Semirings Revisited
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   6 unt;   0 def)
%            Number of atoms       :    6 (   6 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    3 (   3 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   10 (  10 usr;   0 con; 1-2 aty)
%            Number of variables   :   11 (  11   !;   0   ?)
% SPC      : 

% Comments : Requires KLE001+4.ax
%          : With KLE001+0 and KLE001+4.ax generates modal semirings
%            With KLE002+0 and KLE001+4.ax generates modal Kleene Algebra
%            With KLE003+0 and KLE001+4.ax generates modal Omega Algebra
%          : Defines forward/backward box and diamond (and domain).
%------------------------------------------------------------------------------
%----Standard axioms for forward/backward box and diamond
fof(complement,axiom,
    ! [X0] : c(X0) = antidomain(domain(X0)) ).

fof(domain_difference,axiom,
    ! [X0,X1] : domain_difference(X0,X1) = multiplication(domain(X0),antidomain(X1)) ).

fof(forward_diamond,axiom,
    ! [X0,X1] : forward_diamond(X0,X1) = domain(multiplication(X0,domain(X1))) ).

fof(backward_diamond,axiom,
    ! [X0,X1] : backward_diamond(X0,X1) = codomain(multiplication(codomain(X1),X0)) ).

fof(forward_box,axiom,
    ! [X0,X1] : forward_box(X0,X1) = c(forward_diamond(X0,c(X1))) ).

fof(backward_box,axiom,
    ! [X0,X1] : backward_box(X0,X1) = c(backward_diamond(X0,c(X1))) ).

%------------------------------------------------------------------------------

```

### ./KLE001+7.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE001+7 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Divergence Kleene algebras
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [DMS04] Desharnais et al. (2004), Termination in Modal Kleene
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   1 unt;   0 def)
%            Number of atoms       :    3 (   3 equ)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   4 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   0 con; 1-2 aty)
%            Number of variables   :    4 (   4   !;   0   ?)
% SPC      : 

% Comments : Requires KLE001+6.ax KLE002+0.ax
%          : Based on modal Kleene Algebra
%------------------------------------------------------------------------------
fof(divergence1,axiom,
    ! [X0] : forward_diamond(X0,divergence(X0)) = divergence(X0) ).

fof(divergence2,axiom,
    ! [X0,X1,X2] :
      ( addition(domain(X0),addition(forward_diamond(X1,domain(X0)),domain(X2))) = addition(forward_diamond(X1,domain(X0)),domain(X2))
     => addition(domain(X0),addition(divergence(X1),forward_diamond(star(X1),domain(X2)))) = addition(divergence(X1),forward_diamond(star(X1),domain(X2))) ) ).

%------------------------------------------------------------------------------

```

### ./KLE002+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE002+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene algebra
% Axioms   : Kleene algebra
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   16 (  13 unt;   0 def)
%            Number of atoms       :   19 (  12 equ)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    3 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   3 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   30 (  30   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Additive idempotent monoid
fof(additive_commutativity,axiom,
    ! [A,B] : addition(A,B) = addition(B,A) ).

fof(additive_associativity,axiom,
    ! [C,B,A] : addition(A,addition(B,C)) = addition(addition(A,B),C) ).

fof(additive_identity,axiom,
    ! [A] : addition(A,zero) = A ).

fof(additive_idempotence,axiom,
    ! [A] : addition(A,A) = A ).

%----Multiplicative and commutative monoid
fof(multiplicative_associativity,axiom,
    ! [A,B,C] : multiplication(A,multiplication(B,C)) = multiplication(multiplication(A,B),C) ).

fof(multiplicative_right_identity,axiom,
    ! [A] : multiplication(A,one) = A ).

fof(multiplicative_left_identity,axiom,
    ! [A] : multiplication(one,A) = A ).

%----Distributivity laws
fof(right_distributivity,axiom,
    ! [A,B,C] : multiplication(A,addition(B,C)) = addition(multiplication(A,B),multiplication(A,C)) ).

fof(left_distributivity,axiom,
    ! [A,B,C] : multiplication(addition(A,B),C) = addition(multiplication(A,C),multiplication(B,C)) ).

%----Annihilation
fof(right_annihilation,axiom,
    ! [A] : multiplication(A,zero) = zero ).

fof(left_annihilation,axiom,
    ! [A] : multiplication(zero,A) = zero ).

%----Order
fof(order,axiom,
    ! [A,B] :
      ( leq(A,B)
    <=> addition(A,B) = B ) ).

%----Finite iteration (star)

%----Unfold laws
fof(star_unfold_right,axiom,
    ! [A] : leq(addition(one,multiplication(A,star(A))),star(A)) ).

fof(star_unfold_left,axiom,
    ! [A] : leq(addition(one,multiplication(star(A),A)),star(A)) ).

%----Induction laws
fof(star_induction_left,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(A,B),C),B)
     => leq(multiplication(star(A),C),B) ) ).

fof(star_induction_right,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(A,B),C),A)
     => leq(multiplication(C,star(B)),A) ) ).

%------------------------------------------------------------------------------

```

### ./KLE003+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE003+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Omega algebra
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   18 (  14 unt;   0 def)
%            Number of atoms       :   22 (  13 equ)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   3 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-2 aty)
%            Number of variables   :   34 (  34   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Additive idempotent monoid
fof(additive_commutativity,axiom,
    ! [A,B] : addition(A,B) = addition(B,A) ).

fof(additive_associativity,axiom,
    ! [C,B,A] : addition(A,addition(B,C)) = addition(addition(A,B),C) ).

fof(additive_identity,axiom,
    ! [A] : addition(A,zero) = A ).

fof(additive_idempotence,axiom,
    ! [A] : addition(A,A) = A ).

%----Multiplicative and commutative monoid
fof(multiplicative_associativity,axiom,
    ! [A,B,C] : multiplication(A,multiplication(B,C)) = multiplication(multiplication(A,B),C) ).

fof(multiplicative_right_identity,axiom,
    ! [A] : multiplication(A,one) = A ).

fof(multiplicative_left_identity,axiom,
    ! [A] : multiplication(one,A) = A ).

%----Distributivity laws
fof(right_distributivity,axiom,
    ! [A,B,C] : multiplication(A,addition(B,C)) = addition(multiplication(A,B),multiplication(A,C)) ).

fof(left_distributivity,axiom,
    ! [A,B,C] : multiplication(addition(A,B),C) = addition(multiplication(A,C),multiplication(B,C)) ).

%----Annihilation
fof(right_annihilation,axiom,
    ! [A] : multiplication(A,zero) = zero ).

fof(left_annihilation,axiom,
    ! [A] : multiplication(zero,A) = zero ).

%----Order
fof(order,axiom,
    ! [A,B] :
      ( leq(A,B)
    <=> addition(A,B) = B ) ).

%----Finite iteration (star)

%----Unfold laws
fof(star_unfold_right,axiom,
    ! [A] : leq(addition(one,multiplication(A,star(A))),star(A)) ).

fof(star_unfold_left,axiom,
    ! [A] : leq(addition(one,multiplication(star(A),A)),star(A)) ).

%----Induction laws
fof(star_induction_left,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(A,B),C),B)
     => leq(multiplication(star(A),C),B) ) ).

fof(star_induction_right,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(A,B),C),A)
     => leq(multiplication(C,star(B)),A) ) ).

%----Infinite iteration (omega)

%----Unfold law
fof(omega_unfold,axiom,
    ! [A] : multiplication(A,omega(A)) = omega(A) ).

%----Co-Induction law
fof(omega_co_induction,axiom,
    ! [A,B,C] :
      ( leq(A,addition(multiplication(B,A),C))
     => leq(A,addition(omega(B),multiplication(star(B),C))) ) ).

%------------------------------------------------------------------------------

```

### ./KLE004+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : KLE004+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Kleene Algebra
% Axioms   : Demonic Refinement Algebra
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   18 (  14 unt;   0 def)
%            Number of atoms       :   22 (  15 equ)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   3 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-2 aty)
%            Number of variables   :   34 (  34   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Additive idempotent monoid
fof(additive_commutativity,axiom,
    ! [A,B] : addition(A,B) = addition(B,A) ).

fof(additive_associativity,axiom,
    ! [C,B,A] : addition(A,addition(B,C)) = addition(addition(A,B),C) ).

fof(additive_identity,axiom,
    ! [A] : addition(A,zero) = A ).

fof(idempotence,axiom,
    ! [A] : addition(A,A) = A ).

%----Multiplicative and commutative monoid
fof(multiplicative_associativity,axiom,
    ! [A,B,C] : multiplication(A,multiplication(B,C)) = multiplication(multiplication(A,B),C) ).

fof(multiplicative_right_identity,axiom,
    ! [A] : multiplication(A,one) = A ).

fof(multiplicative_left_identity,axiom,
    ! [A] : multiplication(one,A) = A ).

%----Distributivity laws
fof(distributivity1,axiom,
    ! [A,B,C] : multiplication(A,addition(B,C)) = addition(multiplication(A,B),multiplication(A,C)) ).

fof(distributivity2,axiom,
    ! [A,B,C] : multiplication(addition(A,B),C) = addition(multiplication(A,C),multiplication(B,C)) ).

%----Annihilation (right zero law)
fof(left_annihilation,axiom,
    ! [A] : multiplication(zero,A) = zero ).

%----Kleene star
fof(star_unfold1,axiom,
    ! [A] : addition(one,multiplication(A,star(A))) = star(A) ).

fof(star_unfold2,axiom,
    ! [A] : addition(one,multiplication(star(A),A)) = star(A) ).

fof(star_induction1,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(A,C),B),C)
     => leq(multiplication(star(A),B),C) ) ).

fof(star_induction2,axiom,
    ! [A,B,C] :
      ( leq(addition(multiplication(C,A),B),C)
     => leq(multiplication(B,star(A)),C) ) ).

%----Strong iteration
fof(infty_unfold1,axiom,
    ! [A] : strong_iteration(A) = addition(multiplication(A,strong_iteration(A)),one) ).

fof(infty_coinduction,axiom,
    ! [A,B,C] :
      ( leq(C,addition(multiplication(A,C),B))
     => leq(C,multiplication(strong_iteration(A),B)) ) ).

fof(isolation,axiom,
    ! [A] : strong_iteration(A) = addition(star(A),multiplication(strong_iteration(A),zero)) ).

%----Ordering
fof(order,axiom,
    ! [A,B] :
      ( leq(A,B)
    <=> addition(A,B) = B ) ).

%------------------------------------------------------------------------------

```

## Knowledge Representation

### ./KRS001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : KRS001+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Knowledge Representation
% Axioms   : SZS success ontology nodes
% Version  : [Sut08] axioms.
% English  :

% Refs     : [Sut08] Sutcliffe (2008), The SZS Ontologies for Automated Rea
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   19 (   0 unt;   0 def)
%            Number of atoms       :   70 (   0 equ)
%            Maximal formula atoms :    7 (   3 avg)
%            Number of connectives :   63 (  12   ~;   0   |;  24   &)
%                                         (  22 <=>;   5  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :   20 (  20 usr;  19 con; 0-1 aty)
%            Number of variables   :   77 (  49   !;  28   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(unp,axiom,
    ! [Ax,C] :
      ( ( ~ ? [I1] : model(I1,Ax)
       => ~ ? [I2] : model(I2,C) )
    <=> status(Ax,C,unp) ) ).

fof(sap,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
       => ? [I2] : model(I2,C) )
    <=> status(Ax,C,sap) ) ).

fof(esa,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
      <=> ? [I2] : model(I2,C) )
    <=> status(Ax,C,esa) ) ).

fof(sat,axiom,
    ! [Ax,C] :
      ( ? [I1] :
          ( model(I1,Ax)
          & model(I1,C) )
    <=> status(Ax,C,sat) ) ).

fof(thm,axiom,
    ! [Ax,C] :
      ( ! [I1] :
          ( model(I1,Ax)
         => model(I1,C) )
    <=> status(Ax,C,thm) ) ).

fof(eqv,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ! [I2] :
            ( model(I2,Ax)
          <=> model(I2,C) ) )
    <=> status(Ax,C,eqv) ) ).

fof(tac,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ! [I2] : model(I2,C) )
    <=> status(Ax,C,tac) ) ).

fof(wec,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ! [I2] :
            ( model(I2,Ax)
           => model(I2,C) )
        & ? [I3] :
            ( model(I3,C)
            & ~ model(I3,Ax) ) )
    <=> status(Ax,C,wec) ) ).

fof(eth,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ? [I2] : ~ model(I2,Ax)
        & ! [I3] :
            ( model(I3,Ax)
          <=> model(I3,C) ) )
    <=> status(Ax,C,eth) ) ).

fof(tau,axiom,
    ! [Ax,C] :
      ( ! [I1] :
          ( model(I1,Ax)
          & model(I1,C) )
    <=> status(Ax,C,tau) ) ).

fof(wtc,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ? [I2] : ~ model(I2,Ax)
        & ! [I3] : model(I3,C) )
    <=> status(Ax,C,wtc) ) ).

fof(wth,axiom,
    ! [Ax,C] :
      ( ( ? [I1] : model(I1,Ax)
        & ! [I2] :
            ( model(I2,Ax)
           => model(I2,C) )
        & ? [I3] :
            ( model(I3,C)
            & ~ model(I3,Ax) )
        & ? [I4] : ~ model(I4,C) )
    <=> status(Ax,C,wth) ) ).

fof(cax,axiom,
    ! [Ax,C] :
      ( ~ ? [I1] : model(I1,Ax)
    <=> status(Ax,C,cax) ) ).

fof(sca,axiom,
    ! [Ax,C] :
      ( ( ~ ? [I1] : model(I1,Ax)
        & ? [I2] : model(I2,C) )
    <=> status(Ax,C,sca) ) ).

fof(tca,axiom,
    ! [Ax,C] :
      ( ( ~ ? [I1] : model(I1,Ax)
        & ! [I2] : model(I2,C) )
    <=> status(Ax,C,tca) ) ).

fof(wca,axiom,
    ! [Ax,C] :
      ( ( ~ ? [I1] : model(I1,Ax)
        & ? [I2] : model(I2,C)
        & ? [I3] : ~ model(I3,C) )
    <=> status(Ax,C,wca) ) ).

fof(csa,axiom,
    ! [Ax,C] :
      ( ? [I1] :
          ( model(I1,Ax)
          & model(I1,not(C)) )
    <=> status(Ax,C,csa) ) ).

fof(uns,axiom,
    ! [Ax,C] :
      ( ( ! [I1] : model(I1,Ax)
        & ! [I2] : model(I2,not(C)) )
    <=> status(Ax,C,uns) ) ).

fof(noc,axiom,
    ! [Ax,C] :
      ( ( ? [I1] :
            ( model(I1,Ax)
            & model(I1,C) )
        & ? [I2] :
            ( model(I2,Ax)
            & model(I2,not(C)) ) )
    <=> status(Ax,C,noc) ) ).

%------------------------------------------------------------------------------

```

### ./KRS001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : KRS001+1 : TPTP v8.2.0. Bugfixed v5.4.0.
% Domain   : Knowledge Representation
% Axioms   : SZS success ontology node relationships
% Version  : [Sut08] axioms.
% English  :

% Refs     : [Sut08] Sutcliffe (2008), The SZS Ontologies for Automated Rea
% Source   : [Sut08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   13 (   2 unt;   0 def)
%            Number of atoms       :   36 (   0 equ)
%            Maximal formula atoms :    6 (   2 avg)
%            Number of connectives :   33 (  10   ~;   1   |;  11   &)
%                                         (   6 <=>;   3  =>;   0  <=;   2 <~>)
%            Maximal formula depth :    9 (   6 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :   45 (  23   !;  22   ?)
% SPC      : 

% Comments :
% Bugfixes : v5.4.0 - Added mixed_pair axiom.
%------------------------------------------------------------------------------
fof(mighta,axiom,
    ! [S1,S2] :
      ( ? [Ax,C] :
          ( status(Ax,C,S1)
          & status(Ax,C,S2) )
    <=> mighta(S1,S2) ) ).

fof(isa,axiom,
    ! [S1,S2] :
      ( ! [Ax,C] :
          ( status(Ax,C,S1)
         => status(Ax,C,S2) )
    <=> isa(S1,S2) ) ).

fof(nota,axiom,
    ! [S1,S2] :
      ( ? [Ax,C] :
          ( status(Ax,C,S1)
          & ~ status(Ax,C,S2) )
    <=> nota(S1,S2) ) ).

fof(nevera,axiom,
    ! [S1,S2] :
      ( ! [Ax,C] :
          ( status(Ax,C,S1)
         => ~ status(Ax,C,S2) )
    <=> nevera(S1,S2) ) ).

fof(xora,axiom,
    ! [S1,S2] :
      ( ! [Ax,C] :
          ( status(Ax,C,S1)
        <~> status(Ax,C,S2) )
    <=> xora(S1,S2) ) ).

fof(completeness,axiom,
    ! [I,F] :
      ( model(I,F)
    <~> model(I,not(F)) ) ).

fof(not,axiom,
    ! [I,F] :
      ( model(I,F)
    <=> ~ model(I,not(F)) ) ).

fof(tautology,axiom,
    ? [F] :
    ! [I] : model(I,F) ).

fof(satisfiable,axiom,
    ? [F] :
      ( ? [I1] : model(I1,F)
      & ? [I2] : ~ model(I2,F) ) ).

fof(contradiction,axiom,
    ? [F] :
    ! [I] : ~ model(I,F) ).

%----There exist axiom-conjecture pairs for which some interpretations make 
%----both true and some interpretations make neither true.
fof(sat_non_taut_pair,axiom,
    ? [Ax,C] :
      ( ? [I1] :
          ( model(I1,Ax)
          & model(I1,C) )
      & ? [I2] :
          ( ~ model(I2,Ax)
          | ~ model(I2,C) ) ) ).

%----There exist axiom conjecture pairs for which some interpretations make 
%----the axioms true, every interpretation that makes the axioms true makes
%----the conjecture true, some interpretations make only the conjecture true, 
%----and some interpretations don't make the conjecture true.
fof(mixed_pair,axiom,
    ? [Ax,C] :
      ( ? [I1] : model(I1,Ax)
      & ! [I2] :
          ( model(I2,Ax)
         => model(I2,C) )
      & ? [I3] :
          ( ~ model(I3,Ax)
          & model(I3,C) )
      & ? [I4] : ~ model(I4,C) ) ).

%----There exist satisfiable axioms that do not imply a satisfiable conjecture
fof(non_thm_spt,axiom,
    ? [I1,Ax,C] :
      ( model(I1,Ax)
      & ~ model(I1,C)
      & ? [I2] : model(I2,C) ) ).

%------------------------------------------------------------------------------

```

## Lattice Theory

### ./LAT001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory (equality) axioms
% Version  : [McC88] (equality) axioms.
% English  :

% Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic
%          : [McC88] McCune (1988), Challenge Equality Problems in Lattice
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [McC88]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   0 RR)
%            Number of literals    :    8 (   8 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   16 (   2 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----The following 8 clauses characterise lattices
cnf(idempotence_of_meet,axiom,
    meet(X,X) = X ).

cnf(idempotence_of_join,axiom,
    join(X,X) = X ).

cnf(absorption1,axiom,
    meet(X,join(X,Y)) = X ).

cnf(absorption2,axiom,
    join(X,meet(X,Y)) = X ).

cnf(commutativity_of_meet,axiom,
    meet(X,Y) = meet(Y,X) ).

cnf(commutativity_of_join,axiom,
    join(X,Y) = join(Y,X) ).

cnf(associativity_of_meet,axiom,
    meet(meet(X,Y),Z) = meet(X,meet(Y,Z)) ).

cnf(associativity_of_join,axiom,
    join(join(X,Y),Z) = join(X,join(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./LAT001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory modularity (equality) axioms
% Version  : [McC88] (equality) axioms.
% English  :

% Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic
%          : [McC88] McCune (1988), Challenge Equality Problems in Lattice
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [McC88]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   0 RR)
%            Number of literals    :    6 (   6 equ;   1 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :    7 (   2 sgn)
% SPC      : 

% Comments : Requires LAT001-0.ax
%          : These axioms, with 4 extra redundant axioms about 0 & 1, are
%            used in [Wos88] p.217.
%--------------------------------------------------------------------------
%----Include 1 and 0 in the lattice
cnf(x_meet_0,axiom,
    meet(X,n0) = n0 ).

cnf(x_join_0,axiom,
    join(X,n0) = X ).

cnf(x_meet_1,axiom,
    meet(X,n1) = X ).

cnf(x_join_1,axiom,
    join(X,n1) = n1 ).

%----Require the lattice to be modular
cnf(modular,axiom,
    ( meet(X,Z) != X
    | meet(Z,join(X,Y)) = join(X,meet(Y,Z)) ) ).

%--------------------------------------------------------------------------

```

### ./LAT001-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT001-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory complement (equality) axioms
% Version  : [McC88] (equality) axioms.
% English  :

% Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic
%          : [McC88] McCune (1988), Challenge Equality Problems in Lattice
% Source   : [McC88]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   0 unt;   0 nHn;   3 RR)
%            Number of literals    :    7 (   4 equ;   4 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :    6 (   0 sgn)
% SPC      : 

% Comments : Requires LAT001-0.ax
%--------------------------------------------------------------------------
%----Definition of complement
cnf(complement_meet,axiom,
    ( ~ complement(X,Y)
    | meet(X,Y) = n0 ) ).

cnf(complement_join,axiom,
    ( ~ complement(X,Y)
    | join(X,Y) = n1 ) ).

cnf(meet_join_complement,axiom,
    ( meet(X,Y) != n0
    | join(X,Y) != n1
    | complement(X,Y) ) ).

%--------------------------------------------------------------------------

```

### ./LAT001-3.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT001-3 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory unique complement (equality) axioms
% Version  : [McC88] (equality) axioms.
% English  :

% Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic
%          : [McC88] McCune (1988), Challenge Equality Problems in Lattice
% Source   : [McC88]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   0 unt;   1 nHn;   4 RR)
%            Number of literals    :   11 (   2 equ;   6 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :    9 (   0 sgn)
% SPC      : 

% Comments : Requires LAT001-0.ax LAT001-1.ax
%--------------------------------------------------------------------------
%----Definition of unique complement
cnf(unique_complement1,axiom,
    ( ~ unique_complement(X,Y)
    | complement(X,Y) ) ).

cnf(unique_complement2,axiom,
    ( ~ unique_complement(X,Y)
    | ~ complement(X,Z)
    | Z = Y ) ).

cnf(unique_complement3,axiom,
    ( unique_complement(X,Y)
    | ~ complement(X,Y)
    | complement(X,f(X,Y)) ) ).

cnf(unique_complement4,axiom,
    ( unique_complement(X,Y)
    | ~ complement(X,Y)
    | f(X,Y) != Y ) ).

%--------------------------------------------------------------------------

```

### ./LAT001-4.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT001-4 : TPTP v8.2.0. Released .0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory unique complementation (equality) axioms
% Version  : [McC05] (equality) axioms.
% English  :

% Refs     : [McC05] McCune (2005), Email to Geoff Sutcliffe
% Source   : [McC05]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   1 RR)
%            Number of literals    :    5 (   5 equ;   2 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : 

% Comments : Requires LAT001-0.ax
%--------------------------------------------------------------------------
%----Unique complementation
cnf(complement_join,axiom,
    join(X,complement(X)) = one ).

cnf(complement_meet,axiom,
    meet(X,complement(X)) = zero ).

cnf(meet_join_complement,axiom,
    ( meet(X,Y) != zero
    | join(X,Y) != one
    | complement(X) = Y ) ).

%--------------------------------------------------------------------------

```

### ./LAT002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Lattice Theory
% Axioms   : Lattice theory axioms
% Version  : [MOW76] axioms :
%            Incomplete > Reduced & Augmented > Complete.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   20 (   8 unt;   0 nHn;  12 RR)
%            Number of literals    :   48 (   2 equ;  28 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   66 (   4 sgn)
% SPC      : 

% Comments : These axioms are used in [Wos88] p.215, augmented by some
%            redundant axioms about 0 & 1.
%          : The original [MOW76] axioms have two extra redundant
%            modularity axioms.
%          : [OTTER] uses these too, augmented by some redundant axioms.
%          : The [MOW76] axiomatisation is missing the axioms that make
%            join and meet total functions.
%--------------------------------------------------------------------------
%----Union of n1 and x is equal to n1 :  (n1 v X) = n1
cnf(join_1_and_x,axiom,
    join(n1,X,n1) ).

%----Union of x with itself is equal to x :  (X v X) = X
cnf(join_x_and_x,axiom,
    join(X,X,X) ).

%----Union of n0 and x is equal to x :  (n0 v X) = X
cnf(join_0_and_x,axiom,
    join(n0,X,X) ).

%----Intersection of n0 and x is equal to n0 : (n0 ^ X) = n0
cnf(meet_0_and_x,axiom,
    meet(n0,X,n0) ).

%----Intersection of x and itself is equal to x : (X ^ X) = X
cnf(meet_x_and_x,axiom,
    meet(X,X,X) ).

%----Intersection of n1 and x is equal to itself : (n1 ^ X) = X
cnf(meet_1_and_x,axiom,
    meet(n1,X,X) ).

%----Intersection of x and y , is the same as meet of y and x.
%----  (X ^ Y) = (Y ^ X),
cnf(commutativity_of_meet,axiom,
    ( ~ meet(X,Y,Z)
    | meet(Y,X,Z) ) ).

%----Union of x and y is the same as join of y and x. (X v Y) = (Y v X),
cnf(commutativity_of_join,axiom,
    ( ~ join(X,Y,Z)
    | join(Y,X,Z) ) ).

%----Union of x with the meet of x and y is the same as x.
%----  X v (X ^ Y) = X
cnf(absorbtion1,axiom,
    ( ~ meet(X,Y,Z)
    | join(X,Z,X) ) ).

%----Intersection  of x with the join of x and y is the same as x.
%----  X ^ (X v Y) = X
cnf(absorbtion2,axiom,
    ( ~ join(X,Y,Z)
    | meet(X,Z,X) ) ).

%----The operation '^', meet ,is associative
%----  X ^ (Y ^ Z) = (X ^ Y) ^ Z
cnf(associativity_of_meet1,axiom,
    ( ~ meet(X,Y,Xy)
    | ~ meet(Y,Z,Yz)
    | ~ meet(X,Yz,Xyz)
    | meet(Xy,Z,Xyz) ) ).

cnf(associativity_of_meet2,axiom,
    ( ~ meet(X,Y,Xy)
    | ~ meet(Y,Z,Yz)
    | ~ meet(Xy,Z,Xyz)
    | meet(X,Yz,Xyz) ) ).

%----The operation 'v' is associative X v (Y v Z) = (X v Y) v Z
cnf(associativity_of_join1,axiom,
    ( ~ join(X,Y,Xy)
    | ~ join(Y,Z,Yz)
    | ~ join(X,Yz,Xyz)
    | join(Xy,Z,Xyz) ) ).

cnf(associativity_of_join2,axiom,
    ( ~ join(X,Y,Xy)
    | ~ join(Y,Z,Yz)
    | ~ join(Xy,Z,Xyz)
    | join(X,Yz,Xyz) ) ).

%----(X ^ Z) = X implies that (Z ^ (X v Y)) =  (X v (Y ^ Z)),
cnf(modularity1,axiom,
    ( ~ meet(X,Z,X)
    | ~ join(X,Y,X1)
    | ~ meet(Y,Z,Y1)
    | ~ meet(Z,X1,Z1)
    | join(X,Y1,Z1) ) ).

cnf(modularity2,axiom,
    ( ~ meet(X,Z,X)
    | ~ join(X,Y,X1)
    | ~ meet(Y,Z,Y1)
    | ~ join(X,Y1,Z1)
    | meet(Z,X1,Z1) ) ).

cnf(meet_total_function_1,axiom,
    meet(X,Y,meet_of(X,Y)) ).

cnf(meet_total_function_2,axiom,
    ( ~ meet(X,Y,Z1)
    | ~ meet(X,Y,Z2)
    | Z1 = Z2 ) ).

cnf(join_total_function_1,axiom,
    join(X,Y,join_of(X,Y)) ).

cnf(join_total_function_2,axiom,
    ( ~ join(X,Y,Z1)
    | ~ join(X,Y,Z2)
    | Z1 = Z2 ) ).

%--------------------------------------------------------------------------

```

### ./LAT003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT003-0 : TPTP v8.2.0. Bugfixed v2.2.1.
% Domain   : Lattice Theory (Ortholattices)
% Axioms   : Ortholattice theory (equality) axioms
% Version  : [McC98b] (equality) axioms.
% English  :

% Refs     : [McC98a] McCune (1998), Automatic Proofs and Counterexamples f
%          : [McC98b] McCune (1998), Email to G. Sutcliffe
% Source   : [McC98b]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   10 (  10 unt;   0 nHn;   0 RR)
%            Number of literals    :   10 (  10 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   19 (   2 sgn)
% SPC      : 

% Comments :
% Bugfixes : v2.2.1 - Added clauses top and bottom.
%--------------------------------------------------------------------------
%----Axioms for an Ortholattice:
cnf(top,axiom,
    join(complement(X),X) = n1 ).

cnf(bottom,axiom,
    meet(complement(X),X) = n0 ).

cnf(absorption2,axiom,
    join(X,meet(X,Y)) = X ).

cnf(commutativity_of_meet,axiom,
    meet(X,Y) = meet(Y,X) ).

cnf(commutativity_of_join,axiom,
    join(X,Y) = join(Y,X) ).

cnf(associativity_of_meet,axiom,
    meet(meet(X,Y),Z) = meet(X,meet(Y,Z)) ).

cnf(associativity_of_join,axiom,
    join(join(X,Y),Z) = join(X,join(Y,Z)) ).

cnf(complement_involution,axiom,
    complement(complement(X)) = X ).

cnf(join_complement,axiom,
    join(X,join(Y,complement(Y))) = join(Y,complement(Y)) ).

cnf(meet_complement,axiom,
    meet(X,Y) = complement(join(complement(X),complement(Y))) ).

%--------------------------------------------------------------------------

```

### ./LAT004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LAT004-0 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Lattice Theory (Quasilattices)
% Axioms   : Quasilattice theory (equality) axioms
% Version  : [McC98b] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   0 RR)
%            Number of literals    :    8 (   8 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   18 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Quasilattice theory:
cnf(idempotence_of_meet,axiom,
    meet(X,X) = X ).

cnf(idempotence_of_join,axiom,
    join(X,X) = X ).

cnf(commutativity_of_meet,axiom,
    meet(X,Y) = meet(Y,X) ).

cnf(commutativity_of_join,axiom,
    join(X,Y) = join(Y,X) ).

cnf(associativity_of_meet,axiom,
    meet(meet(X,Y),Z) = meet(X,meet(Y,Z)) ).

cnf(associativity_of_join,axiom,
    join(join(X,Y),Z) = join(X,join(Y,Z)) ).

cnf(quasi_lattice1,axiom,
    join(meet(X,join(Y,Z)),meet(X,Y)) = meet(X,join(Y,Z)) ).

cnf(quasi_lattice2,axiom,
    meet(join(X,meet(Y,Z)),join(X,Y)) = join(X,meet(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./LAT005-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LAT005-0 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Lattice Theory (Weakly Associative Lattices)
% Axioms   : Weakly Associative Lattices theory (equality) axioms
% Version  : [McC98b] (equality) axioms.
% English  :

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   0 RR)
%            Number of literals    :    6 (   6 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   12 (   4 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Axioms for a weakly associative lattice:
cnf(idempotence_of_meet,axiom,
    meet(X,X) = X ).

cnf(idempotence_of_join,axiom,
    join(X,X) = X ).

cnf(commutativity_of_meet,axiom,
    meet(X,Y) = meet(Y,X) ).

cnf(commutativity_of_join,axiom,
    join(X,Y) = join(Y,X) ).

cnf(wal_1,axiom,
    meet(meet(join(X,Y),join(Z,Y)),Y) = Y ).

cnf(wal_2,axiom,
    join(join(meet(X,Y),meet(Z,Y)),Y) = Y ).

%------------------------------------------------------------------------------

```

### ./LAT006-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LAT006-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Lattice Theory
% Axioms   : Tarski's fixed point theorem (equality) axioms
% Version  : [Pau06] (equality) axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Tarski.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    9 (   6 unt;   0 nHn;   3 RR)
%            Number of literals    :   12 (  12 equ;   3 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   7 usr;   0 con; 3-5 aty)
%            Number of variables   :   56 (  21 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
cnf(cls_Tarski_Opotype_Oext__inject_0,axiom,
    ( c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z) != c_Tarski_Opotype_Opotype__ext(V_pset_H,V_order_H,V_more_H,T_a,T_z)
    | V_pset = V_pset_H ) ).

cnf(cls_Tarski_Opotype_Oext__inject_1,axiom,
    ( c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z) != c_Tarski_Opotype_Opotype__ext(V_pset_H,V_order_H,V_more_H,T_a,T_z)
    | V_order = V_order_H ) ).

cnf(cls_Tarski_Opotype_Oext__inject_2,axiom,
    ( c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z) != c_Tarski_Opotype_Opotype__ext(V_pset_H,V_order_H,V_more_H,T_a,T_z)
    | V_more = V_more_H ) ).

cnf(cls_Tarski_Opotype_Oselect__convs__1_0,axiom,
    c_Tarski_Opotype_Opset(c_Tarski_Opotype_Opotype__ext(V_y,V_order,V_more,T_a,T_z),T_a,T_z) = V_y ).

cnf(cls_Tarski_Opotype_Oselect__convs__2_0,axiom,
    c_Tarski_Opotype_Oorder(c_Tarski_Opotype_Opotype__ext(V_pset,V_y,V_more,T_a,T_z),T_a,T_z) = V_y ).

cnf(cls_Tarski_Opotype_Oselect__convs__3_0,axiom,
    c_Tarski_Opotype_Omore(c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_y,T_a,T_a),T_a,T_a) = V_y ).

cnf(cls_Tarski_Opotype_Oupdate__convs__1_0,axiom,
    c_Tarski_Opotype_Opset__update(V_pset_H,c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z),T_a,T_z) = c_Tarski_Opotype_Opotype__ext(V_pset_H,V_order,V_more,T_a,T_z) ).

cnf(cls_Tarski_Opotype_Oupdate__convs__2_0,axiom,
    c_Tarski_Opotype_Oorder__update(V_order_H,c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z),T_a,T_z) = c_Tarski_Opotype_Opotype__ext(V_pset,V_order_H,V_more,T_a,T_z) ).

cnf(cls_Tarski_Opotype_Oupdate__convs__3_0,axiom,
    c_Tarski_Opotype_Omore__update(V_more_H,c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more,T_a,T_z),T_z,T_a) = c_Tarski_Opotype_Opotype__ext(V_pset,V_order,V_more_H,T_a,T_z) ).

%------------------------------------------------------------------------------

```

### ./LAT006-1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LAT006-1 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Lattice Theory
% Axioms   : Tarski's fixed point theorem GLB (equality) axioms
% Version  : [Pau06] (equality) axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Tarski__glb.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   13 (   7 unt;   0 nHn;  11 RR)
%            Number of literals    :   22 (   4 equ;   9 neg)
%            Maximal clause size   :    5 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 2-3 aty)
%            Number of functors    :   16 (  16 usr;   7 con; 0-4 aty)
%            Number of variables   :   23 (   0 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
cnf(cls_Tarski_OA_A_61_61_Apset_Acl_0,axiom,
    v_A = c_Tarski_Opotype_Opset(v_cl,t_a,tc_Product__Type_Ounit) ).

cnf(cls_Tarski_OCL_Olub__upper_0,axiom,
    ( ~ c_in(V_x,V_S,T_a)
    | ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | ~ c_in(V_cl,c_Tarski_OPartialOrder,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | ~ c_lessequals(V_S,c_Tarski_Opotype_Opset(V_cl,T_a,tc_Product__Type_Ounit),tc_set(T_a))
    | c_in(c_Pair(V_x,c_Tarski_Olub(V_S,V_cl,T_a),T_a,T_a),c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),tc_prod(T_a,T_a)) ) ).

cnf(cls_Tarski_O_Ix1_M_Ay1_J_A_58_Aorder_A_Idual_Acl_J_A_61_61_A_Iy1_M_Ax1_J_A_58_Aorder_Acl_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,T_a,T_a),c_Tarski_Opotype_Oorder(c_Tarski_Odual(V_cl,T_a),T_a,tc_Product__Type_Ounit),tc_prod(T_a,T_a))
    | c_in(c_Pair(V_y,V_x,T_a,T_a),c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),tc_prod(T_a,T_a)) ) ).

cnf(cls_Tarski_O_Ix1_M_Ay1_J_A_58_Aorder_A_Idual_Acl_J_A_61_61_A_Iy1_M_Ax1_J_A_58_Aorder_Acl_1,axiom,
    ( ~ c_in(c_Pair(V_y,V_x,T_a,T_a),c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),tc_prod(T_a,T_a))
    | c_in(c_Pair(V_x,V_y,T_a,T_a),c_Tarski_Opotype_Oorder(c_Tarski_Odual(V_cl,T_a),T_a,tc_Product__Type_Ounit),tc_prod(T_a,T_a)) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Aantisym_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Oantisym(c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Arefl_A_Ipset_Acl1_J_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Orefl(c_Tarski_Opotype_Opset(V_cl,T_a,tc_Product__Type_Ounit),c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Atrans_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Otrans(c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl_A_58_ACompleteLattice_A_61_61_ATrue_0,axiom,
    c_in(v_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(t_a,tc_Product__Type_Ounit)) ).

cnf(cls_Tarski_Odual_Acl_A_58_ACompleteLattice_0,axiom,
    c_in(c_Tarski_Odual(v_cl,t_a),c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(t_a,tc_Product__Type_Ounit)) ).

cnf(cls_Tarski_Odual_Acl_A_58_APartialOrder_0,axiom,
    c_in(c_Tarski_Odual(v_cl,t_a),c_Tarski_OPartialOrder,tc_Tarski_Opotype_Opotype__ext__type(t_a,tc_Product__Type_Ounit)) ).

cnf(cls_Tarski_Oglb__dual__lub_0,axiom,
    c_Tarski_Oglb(V_S,V_cl,T_a) = c_Tarski_Olub(V_S,c_Tarski_Odual(V_cl,T_a),T_a) ).

cnf(cls_Tarski_Opset_A_Idual_Acl_J_A_61_61_Apset_Acl_0,axiom,
    c_Tarski_Opotype_Opset(c_Tarski_Odual(V_cl,T_a),T_a,tc_Product__Type_Ounit) = c_Tarski_Opotype_Opset(V_cl,T_a,tc_Product__Type_Ounit) ).

cnf(cls_Tarski_Or_A_61_61_Aorder_Acl_0,axiom,
    v_r = c_Tarski_Opotype_Oorder(v_cl,t_a,tc_Product__Type_Ounit) ).

%------------------------------------------------------------------------------

```

### ./LAT006-2.ax

```vampire
%------------------------------------------------------------------------------
% File     : LAT006-2 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Lattice Theory
% Axioms   : Tarski's fixed point theorem L (equality) axioms
% Version  : [Pau06] (equality) axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Tarski__L.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   15 (   1 unt;   5 nHn;  12 RR)
%            Number of literals    :   51 (   4 equ;  27 neg)
%            Maximal clause size   :    5 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    7 (   6 usr;   0 prp; 2-4 aty)
%            Number of functors    :   17 (  17 usr;   7 con; 0-4 aty)
%            Number of variables   :   51 (   6 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
cnf(cls_Tarski_O_91_124_AS1_A_60_61_AA_59_AS1_A_126_61_A_123_125_59_AALL_Ax_58S1_O_A_Ia1_M_Ax_J_A_58_Ar_59_AALL_Ay_58S1_O_A_Iy_M_AL1_J_A_58_Ar_A_124_93_A_61_61_62_A_Ia1_M_AL1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_lessequals(V_S,V_A,tc_set(t_a))
    | c_in(c_Pair(V_a,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | c_in(v_sko__4mj(V_S,V_a,v_r),V_S,t_a)
    | c_in(v_sko__4mk(V_L,V_S,v_r),V_S,t_a)
    | V_S = c_emptyset ) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_AA_59_AS1_A_126_61_A_123_125_59_AALL_Ax_58S1_O_A_Ia1_M_Ax_J_A_58_Ar_59_AALL_Ay_58S1_O_A_Iy_M_AL1_J_A_58_Ar_A_124_93_A_61_61_62_A_Ia1_M_AL1_J_A_58_Ar_A_61_61_ATrue_1,axiom,
    ( ~ c_in(c_Pair(v_sko__4mk(V_L,V_S,v_r),V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | ~ c_lessequals(V_S,V_A,tc_set(t_a))
    | c_in(c_Pair(V_a,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | c_in(v_sko__4mj(V_S,V_a,v_r),V_S,t_a)
    | V_S = c_emptyset ) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_AA_59_AS1_A_126_61_A_123_125_59_AALL_Ax_58S1_O_A_Ia1_M_Ax_J_A_58_Ar_59_AALL_Ay_58S1_O_A_Iy_M_AL1_J_A_58_Ar_A_124_93_A_61_61_62_A_Ia1_M_AL1_J_A_58_Ar_A_61_61_ATrue_2,axiom,
    ( ~ c_in(c_Pair(V_a,v_sko__4mj(V_S,V_a,v_r),t_a,t_a),v_r,tc_prod(t_a,t_a))
    | ~ c_lessequals(V_S,V_A,tc_set(t_a))
    | c_in(c_Pair(V_a,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | c_in(v_sko__4mk(V_L,V_S,v_r),V_S,t_a)
    | V_S = c_emptyset ) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_AA_59_AS1_A_126_61_A_123_125_59_AALL_Ax_58S1_O_A_Ia1_M_Ax_J_A_58_Ar_59_AALL_Ay_58S1_O_A_Iy_M_AL1_J_A_58_Ar_A_124_93_A_61_61_62_A_Ia1_M_AL1_J_A_58_Ar_A_61_61_ATrue_3,axiom,
    ( ~ c_in(c_Pair(V_a,v_sko__4mj(V_S,V_a,v_r),t_a,t_a),v_r,tc_prod(t_a,t_a))
    | ~ c_in(c_Pair(v_sko__4mk(V_L,V_S,v_r),V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | ~ c_lessequals(V_S,V_A,tc_set(t_a))
    | c_in(c_Pair(V_a,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | V_S = c_emptyset ) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_Ainterval_Ar_Aa1_Ab1_59_Ax1_A_58_AS1_A_124_93_A_61_61_62_A_Ia1_M_Ax1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_x,V_S,T_a)
    | ~ c_lessequals(V_S,c_Tarski_Ointerval(V_r,V_a,V_b,T_a),tc_set(T_a))
    | c_in(c_Pair(V_a,V_x,T_a,T_a),V_r,tc_prod(T_a,T_a)) ) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_Ainterval_Ar_Aa1_Ab1_59_Ax1_A_58_AS1_A_124_93_A_61_61_62_A_Ix1_M_Ab1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_x,V_S,T_a)
    | ~ c_lessequals(V_S,c_Tarski_Ointerval(V_r,V_a,V_b,T_a),tc_set(T_a))
    | c_in(c_Pair(V_x,V_b,T_a,T_a),V_r,tc_prod(T_a,T_a)) ) ).

cnf(cls_Tarski_O_91_124_A_Ia1_M_Ax1_J_A_58_Ar_59_A_Ix1_M_Ab1_J_A_58_Ar_A_124_93_A_61_61_62_Ax1_A_58_Ainterval_Ar_Aa1_Ab1_A_61_61_ATrue_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_b,T_a,T_a),V_r,tc_prod(T_a,T_a))
    | ~ c_in(c_Pair(V_a,V_x,T_a,T_a),V_r,tc_prod(T_a,T_a))
    | c_in(V_x,c_Tarski_Ointerval(V_r,V_a,V_b,T_a),T_a) ) ).

cnf(cls_Tarski_O_91_124_Aa1_A_58_AA_59_Ab1_A_58_AA_59_AS1_A_60_61_Ainterval_Ar_Aa1_Ab1_A_124_93_A_61_61_62_AS1_A_60_61_AA_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_b,v_A,t_a)
    | ~ c_in(V_a,v_A,t_a)
    | ~ c_lessequals(V_S,c_Tarski_Ointerval(v_r,V_a,V_b,t_a),tc_set(t_a))
    | c_lessequals(V_S,v_A,tc_set(t_a)) ) ).

cnf(cls_Tarski_O_91_124_AisLub_AS1_Acl_AL1_59_Ay1_A_58_AS1_A_124_93_A_61_61_62_A_Iy1_M_AL1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_Tarski_OisLub(V_S,v_cl,V_L,t_a)
    | ~ c_in(V_y,V_S,t_a)
    | c_in(c_Pair(V_y,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a)) ) ).

cnf(cls_Tarski_O_91_124_AisLub_AS1_Acl_AL1_59_Az1_A_58_AA_59_AALL_Ay_58S1_O_A_Iy_M_Az1_J_A_58_Ar_A_124_93_A_61_61_62_A_IL1_M_Az1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_Tarski_OisLub(V_S,v_cl,V_L,t_a)
    | ~ c_in(V_z,v_A,t_a)
    | c_in(c_Pair(V_L,V_z,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | c_in(v_sko__4mi(V_S,v_r,V_z),V_S,t_a) ) ).

cnf(cls_Tarski_O_91_124_AisLub_AS1_Acl_AL1_59_Az1_A_58_AA_59_AALL_Ay_58S1_O_A_Iy_M_Az1_J_A_58_Ar_A_124_93_A_61_61_62_A_IL1_M_Az1_J_A_58_Ar_A_61_61_ATrue_1,axiom,
    ( ~ c_Tarski_OisLub(V_S,v_cl,V_L,t_a)
    | ~ c_in(V_z,v_A,t_a)
    | ~ c_in(c_Pair(v_sko__4mi(V_S,v_r,V_z),V_z,t_a,t_a),v_r,tc_prod(t_a,t_a))
    | c_in(c_Pair(V_L,V_z,t_a,t_a),v_r,tc_prod(t_a,t_a)) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Aantisym_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Oantisym(c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Arefl_A_Ipset_Acl1_J_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Orefl(c_Tarski_Opotype_Opset(V_cl,T_a,tc_Product__Type_Ounit),c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl1_A_58_ACompleteLattice_A_61_61_62_Atrans_A_Iorder_Acl1_J_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(T_a,tc_Product__Type_Ounit))
    | c_Relation_Otrans(c_Tarski_Opotype_Oorder(V_cl,T_a,tc_Product__Type_Ounit),T_a) ) ).

cnf(cls_Tarski_Ocl_A_58_ACompleteLattice_A_61_61_ATrue_0,axiom,
    c_in(v_cl,c_Tarski_OCompleteLattice,tc_Tarski_Opotype_Opotype__ext__type(t_a,tc_Product__Type_Ounit)) ).

%------------------------------------------------------------------------------

```

## Logic Calculi

### ./LCL001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Wajsberg Algebras)
% Axioms   : Wajsberg algebra
% Version  : [Bon91] (equality) axioms.
% English  :

% Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras
%          : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic
%          : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
% Source   : [MW92]
% Names    : MV Sentential Calculus [MW92]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   4 unt;   0 nHn;   0 RR)
%            Number of literals    :    4 (   4 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    8 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(wajsberg_1,axiom,
    implies(truth,X) = X ).

cnf(wajsberg_2,axiom,
    implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))) = truth ).

cnf(wajsberg_3,axiom,
    implies(implies(X,Y),Y) = implies(implies(Y,X),X) ).

cnf(wajsberg_4,axiom,
    implies(implies(not(X),not(Y)),implies(Y,X)) = truth ).

%--------------------------------------------------------------------------

```

### ./LCL001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Wajsberg Algebras)
% Axioms   : Wajsberg algebra lattice structure definitions
% Version  : [Bon91] (equality) axioms.
% English  :

% Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras
%          : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic
% Source   : [Bon91]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   4 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-2 aty)
%            Number of variables   :    8 (   0 sgn)
% SPC      : 

% Comments : Requires LCL001-0.ax
%--------------------------------------------------------------------------
%----Definitions of big_V and big_hat
cnf(big_V_definition,axiom,
    big_V(X,Y) = implies(implies(X,Y),Y) ).

cnf(big_hat_definition,axiom,
    big_hat(X,Y) = not(big_V(not(X),not(Y))) ).

%----Definition of partial order
cnf(partial_order_definition1,axiom,
    ( ~ ordered(X,Y)
    | implies(X,Y) = truth ) ).

cnf(partial_order_definition2,axiom,
    ( implies(X,Y) != truth
    | ordered(X,Y) ) ).

%--------------------------------------------------------------------------

```

### ./LCL001-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL001-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Wajsberg Algebras)
% Axioms   : Wajsberg algebra AND and OR definitions
% Version  : [AB90] (equality) axioms.
% English  :

% Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras
%          : [AB90]  Anantharaman & Bonacina (1990), An Application of the
%          : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic
% Source   : [Bon91]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   0 RR)
%            Number of literals    :    6 (   6 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :   14 (   0 sgn)
% SPC      : 

% Comments : Requires LCL001-0.ax
%--------------------------------------------------------------------------
%----Definitions of or and and, which are AC
cnf(or_definition,axiom,
    or(X,Y) = implies(not(X),Y) ).

cnf(or_associativity,axiom,
    or(or(X,Y),Z) = or(X,or(Y,Z)) ).

cnf(or_commutativity,axiom,
    or(X,Y) = or(Y,X) ).

cnf(and_definition,axiom,
    and(X,Y) = not(or(not(X),not(Y))) ).

cnf(and_associativity,axiom,
    and(and(X,Y),Z) = and(X,and(Y,Z)) ).

cnf(and_commutativity,axiom,
    and(X,Y) = and(Y,X) ).

%--------------------------------------------------------------------------

```

### ./LCL002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Wajsberg Algebras)
% Axioms   : Alternative Wajsberg algebra
% Version  : [AB90] (equality) axioms.
% English  :

% Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras
%          : [AB90]  Anantharaman & Bonacina (1990), An Application of the
%          : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic
% Source   : [Bon91]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   0 RR)
%            Number of literals    :    8 (   8 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   10 (   1 sgn)
% SPC      : 

% Comments : Requires LAT003-0.ax
%--------------------------------------------------------------------------
cnf(axiom_1,axiom,
    not(X) = xor(X,truth) ).

cnf(axiom_2,axiom,
    xor(X,falsehood) = X ).

cnf(axiom_3,axiom,
    xor(X,X) = falsehood ).

cnf(axiom_4,axiom,
    and_star(X,truth) = X ).

cnf(axiom_5,axiom,
    and_star(X,falsehood) = falsehood ).

cnf(axiom_6,axiom,
    and_star(xor(truth,X),X) = falsehood ).

cnf(axiom_7,axiom,
    xor(X,xor(truth,Y)) = xor(xor(X,truth),Y) ).

cnf(axiom_8,axiom,
    and_star(xor(and_star(xor(truth,X),Y),truth),Y) = and_star(xor(and_star(xor(truth,Y),X),truth),X) ).

%--------------------------------------------------------------------------

```

### ./LCL002-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL002-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Wajsberg Algebras)
% Axioms   : Alternative Wajsberg algebra definitions
% Version  : [AB90] (equality) axioms.
% English  :

% Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras
%          : [AB90]  Anantharaman & Bonacina (1990), An Application of the
%          : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic
% Source   : [Bon91]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   1 RR)
%            Number of literals    :    6 (   6 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   7 usr;   2 con; 0-2 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : 

% Comments : Requires LCL001-0.ax LCL001-2.ax
%--------------------------------------------------------------------------
%----Definitions of and_star and xor, where and_star is AC and xor is C
cnf(xor_definition,axiom,
    xor(X,Y) = or(and(X,not(Y)),and(not(X),Y)) ).

cnf(xor_commutativity,axiom,
    xor(X,Y) = xor(Y,X) ).

cnf(and_star_definition,axiom,
    and_star(X,Y) = not(or(not(X),not(Y))) ).

%---I guess the next two can be derived from the AC of and
cnf(and_star_associativity,axiom,
    and_star(and_star(X,Y),Z) = and_star(X,and_star(Y,Z)) ).

cnf(and_star_commutativity,axiom,
    and_star(X,Y) = and_star(Y,X) ).

%----Definition of false in terms of truth
cnf(false_definition,axiom,
    not(truth) = falsehood ).

%--------------------------------------------------------------------------

```

### ./LCL003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic deduction
% Version  : [WR27] axioms : Reduced & Augmented.
% English  :

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
%          : [ORo89] O'Rourke (1989), LT Revisited: Explanation-Based Learn
%          : [SE94]  Segre & Elkan (1994), A High-Performance Explanation-B
% Source   : [SE94]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   5 unt;   0 nHn;   3 RR)
%            Number of literals    :   13 (   0 equ;   5 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-1 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 1-2 aty)
%            Number of variables   :   17 (   1 sgn)
% SPC      : 

% Comments : Reduced to use only or and not, and includes a redundant rule
%            of transitivity of implication, and a reduced rule of
%            detachment.
%--------------------------------------------------------------------------
cnf(axiom_1_2,axiom,
    axiom(or(not(or(A,A)),A)) ).

cnf(axiom_1_3,axiom,
    axiom(or(not(A),or(B,A))) ).

cnf(axiom_1_4,axiom,
    axiom(or(not(or(A,B)),or(B,A))) ).

cnf(axiom_1_5,axiom,
    axiom(or(not(or(A,or(B,C))),or(B,or(A,C)))) ).

cnf(axiom_1_6,axiom,
    axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B)))) ).

cnf(rule_1,axiom,
    ( theorem(X)
    | ~ axiom(X) ) ).

cnf(rule_2,axiom,
    ( theorem(X)
    | ~ axiom(or(not(Y),X))
    | ~ theorem(Y) ) ).

cnf(rule_3,axiom,
    ( theorem(or(not(X),Z))
    | ~ axiom(or(not(X),Y))
    | ~ theorem(or(not(Y),Z)) ) ).

%--------------------------------------------------------------------------

```

### ./LCL004-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL004-0 : TPTP v8.2.0. Released v2.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic deduction
% Version  : [WR27] axioms.
% English  :

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
% Source   : [WR27]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   6 unt;   0 nHn;   2 RR)
%            Number of literals    :   11 (   1 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   16 (   1 sgn)
% SPC      : 

% Comments : This axiomatization follows [WR27], allowing full detachment
%            but no chaining (which is a dependant theorem). Compare with
%            LCL003-0.ax.
%------------------------------------------------------------------------------
cnf(axiom_1_2,axiom,
    axiom(implies(or(A,A),A)) ).

cnf(axiom_1_3,axiom,
    axiom(implies(A,or(B,A))) ).

cnf(axiom_1_4,axiom,
    axiom(implies(or(A,B),or(B,A))) ).

cnf(axiom_1_5,axiom,
    axiom(implies(or(A,or(B,C)),or(B,or(A,C)))) ).

cnf(axiom_1_6,axiom,
    axiom(implies(implies(A,B),implies(or(C,A),or(C,B)))) ).

cnf(implies_definition,axiom,
    implies(X,Y) = or(not(X),Y) ).

cnf(rule_1,axiom,
    ( theorem(X)
    | ~ axiom(X) ) ).

cnf(rule_2,axiom,
    ( theorem(X)
    | ~ theorem(implies(Y,X))
    | ~ theorem(Y) ) ).

% input_clause(rule_3,axiom,
%     [++theorem(implies(X,Z)),
%      --theorem(implies(X,Y)),
%      --theorem(implies(Y,Z))]).
%------------------------------------------------------------------------------

```

### ./LCL004-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL004-1 : TPTP v8.2.0. Released v2.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic deduction axioms for AND
% Version  : [WR27] axioms.
% English  :

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
% Source   : [WR27]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   1 unt;   0 nHn;   0 RR)
%            Number of literals    :    1 (   1 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :    2 (   0 sgn)
% SPC      : 

% Comments : Requires LCL004-0.ax
%--------------------------------------------------------------------------
cnf(and_defn,axiom,
    and(P,Q) = not(or(not(P),not(Q))) ).

%--------------------------------------------------------------------------

```

### ./LCL004-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : LCL004-2 : TPTP v8.2.0. Released v2.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic deduction axioms for EQUIVALENT
% Version  : [WR27] axioms.
% English  :

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
% Source   : [WR27]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    1 (   1 unt;   0 nHn;   0 RR)
%            Number of literals    :    1 (   1 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 2-2 aty)
%            Number of variables   :    2 (   0 sgn)
% SPC      : 

% Comments : Requires LCL004-0.ax LCL004-1.ax
%--------------------------------------------------------------------------
cnf(equivalent_defn,axiom,
    equivalent(P,Q) = and(implies(P,Q),implies(Q,P)) ).

%--------------------------------------------------------------------------

```

### ./LCL005-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL005-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : PropLog.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   10 (   6 unt;   0 nHn;  10 RR)
%            Number of literals    :   14 (  12 equ;  10 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-3 aty)
%            Number of variables   :   34 (  20 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax
%------------------------------------------------------------------------------
cnf(cls_PropLog_Opl_Odistinct__1__iff1_0,axiom,
    c_PropLog_Opl_Ofalse != c_PropLog_Opl_Ovar(V_a_H,T_a) ).

cnf(cls_PropLog_Opl_Odistinct__2__iff1_0,axiom,
    c_PropLog_Opl_Ovar(V_a_H,T_a) != c_PropLog_Opl_Ofalse ).

cnf(cls_PropLog_Opl_Odistinct__3__iff1_0,axiom,
    c_PropLog_Opl_Ofalse != c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a) ).

cnf(cls_PropLog_Opl_Odistinct__4__iff1_0,axiom,
    c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a) != c_PropLog_Opl_Ofalse ).

cnf(cls_PropLog_Opl_Odistinct__5__iff1_0,axiom,
    c_PropLog_Opl_Ovar(V_a,T_a) != c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a) ).

cnf(cls_PropLog_Opl_Odistinct__6__iff1_0,axiom,
    c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a) != c_PropLog_Opl_Ovar(V_a,T_a) ).

cnf(cls_PropLog_Opl_Oinject__1__iff1_0,axiom,
    ( c_PropLog_Opl_Ovar(V_a,T_a) != c_PropLog_Opl_Ovar(V_a_H,T_a)
    | V_a = V_a_H ) ).

cnf(cls_PropLog_Opl_Oinject__2__iff1_0,axiom,
    ( c_PropLog_Opl_Oop_A_N_62(V_pl1,V_pl2,T_a) != c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a)
    | V_pl1 = V_pl1_H ) ).

cnf(cls_PropLog_Opl_Oinject__2__iff1_1,axiom,
    ( c_PropLog_Opl_Oop_A_N_62(V_pl1,V_pl2,T_a) != c_PropLog_Opl_Oop_A_N_62(V_pl1_H,V_pl2_H,T_a)
    | V_pl2 = V_pl2_H ) ).

cnf(cls_PropLog_Othms_OH_0,axiom,
    ( ~ c_in(V_p,V_H,tc_PropLog_Opl(T_a))
    | c_in(V_p,c_PropLog_Othms(V_H,T_a),tc_PropLog_Opl(T_a)) ) ).

%------------------------------------------------------------------------------

```

### ./LCL006+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+0 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic rules and axioms
% Version  : [She06] axioms.
% English  :

% Refs     : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [She06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   26 (   0 unt;   0 def)
%            Number of atoms       :   55 (   1 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   29 (   0   ~;   0   |;   1   &)
%                                         (  26 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   4 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :   28 (  27 usr;  26 prp; 0-2 aty)
%            Number of functors    :    5 (   5 usr;   0 con; 1-2 aty)
%            Number of variables   :   55 (  55   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----The only explicit rule of PC. Uniform substitution is implemented by
%----universal quantification
fof(modus_ponens,axiom,
    ( modus_ponens
  <=> ! [X,Y] :
        ( ( is_a_theorem(X)
          & is_a_theorem(implies(X,Y)) )
       => is_a_theorem(Y) ) ) ).

%----Meta-rule of PC, which Ted says is not necessary
fof(substitution_of_equivalents,axiom,
    ( substitution_of_equivalents
  <=> ! [X,Y] :
        ( is_a_theorem(equiv(X,Y))
       => X = Y ) ) ).

%----The axioms of Hilbert PC
fof(modus_tollens,axiom,
    ( modus_tollens
  <=> ! [X,Y] : is_a_theorem(implies(implies(not(Y),not(X)),implies(X,Y))) ) ).

fof(implies_1,axiom,
    ( implies_1
  <=> ! [X,Y] : is_a_theorem(implies(X,implies(Y,X))) ) ).

fof(implies_2,axiom,
    ( implies_2
  <=> ! [X,Y] : is_a_theorem(implies(implies(X,implies(X,Y)),implies(X,Y))) ) ).

fof(implies_3,axiom,
    ( implies_3
  <=> ! [X,Y,Z] : is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z)))) ) ).

fof(and_1,axiom,
    ( and_1
  <=> ! [X,Y] : is_a_theorem(implies(and(X,Y),X)) ) ).

fof(and_2,axiom,
    ( and_2
  <=> ! [X,Y] : is_a_theorem(implies(and(X,Y),Y)) ) ).

fof(and_3,axiom,
    ( and_3
  <=> ! [X,Y] : is_a_theorem(implies(X,implies(Y,and(X,Y)))) ) ).

fof(or_1,axiom,
    ( or_1
  <=> ! [X,Y] : is_a_theorem(implies(X,or(X,Y))) ) ).

fof(or_2,axiom,
    ( or_2
  <=> ! [X,Y] : is_a_theorem(implies(Y,or(X,Y))) ) ).

fof(or_3,axiom,
    ( or_3
  <=> ! [X,Y,Z] : is_a_theorem(implies(implies(X,Z),implies(implies(Y,Z),implies(or(X,Y),Z)))) ) ).

fof(equivalence_1,axiom,
    ( equivalence_1
  <=> ! [X,Y] : is_a_theorem(implies(equiv(X,Y),implies(X,Y))) ) ).

fof(equivalence_2,axiom,
    ( equivalence_2
  <=> ! [X,Y] : is_a_theorem(implies(equiv(X,Y),implies(Y,X))) ) ).

fof(equivalence_3,axiom,
    ( equivalence_3
  <=> ! [X,Y] : is_a_theorem(implies(implies(X,Y),implies(implies(Y,X),equiv(X,Y)))) ) ).

%----Axioms for Rosser
fof(kn1,axiom,
    ( kn1
  <=> ! [P] : is_a_theorem(implies(P,and(P,P))) ) ).

fof(kn2,axiom,
    ( kn2
  <=> ! [P,Q] : is_a_theorem(implies(and(P,Q),P)) ) ).

fof(kn3,axiom,
    ( kn3
  <=> ! [P,Q,R] : is_a_theorem(implies(implies(P,Q),implies(not(and(Q,R)),not(and(R,P))))) ) ).

%----Axioms for Luka
fof(cn1,axiom,
    ( cn1
  <=> ! [P,Q,R] : is_a_theorem(implies(implies(P,Q),implies(implies(Q,R),implies(P,R)))) ) ).

fof(cn2,axiom,
    ( cn2
  <=> ! [P,Q] : is_a_theorem(implies(P,implies(not(P),Q))) ) ).

fof(cn3,axiom,
    ( cn3
  <=> ! [P] : is_a_theorem(implies(implies(not(P),P),P)) ) ).

%----Axioms for Principia
fof(r1,axiom,
    ( r1
  <=> ! [P] : is_a_theorem(implies(or(P,P),P)) ) ).

fof(r2,axiom,
    ( r2
  <=> ! [P,Q] : is_a_theorem(implies(Q,or(P,Q))) ) ).

fof(r3,axiom,
    ( r3
  <=> ! [P,Q] : is_a_theorem(implies(or(P,Q),or(Q,P))) ) ).

%----This is the dependent one
fof(r4,axiom,
    ( r4
  <=> ! [P,Q,R] : is_a_theorem(implies(or(P,or(Q,R)),or(Q,or(P,R)))) ) ).

fof(r5,axiom,
    ( r5
  <=> ! [P,Q,R] : is_a_theorem(implies(implies(Q,R),implies(or(P,Q),or(P,R)))) ) ).

%------------------------------------------------------------------------------

```

### ./LCL006+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+1 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Propositional logic definitions
% Version  : [She06] axioms.
% English  :

% Refs     : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [She06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   0 unt;   0 def)
%            Number of atoms       :   10 (   5 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    5 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   4 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    6 (   5 usr;   5 prp; 0-2 aty)
%            Number of functors    :    5 (   5 usr;   0 con; 1-2 aty)
%            Number of variables   :   10 (  10   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Definitions
fof(op_or,axiom,
    ( op_or
   => ! [X,Y] : or(X,Y) = not(and(not(X),not(Y))) ) ).

fof(op_and,axiom,
    ( op_and
   => ! [X,Y] : and(X,Y) = not(or(not(X),not(Y))) ) ).

fof(op_implies_and,axiom,
    ( op_implies_and
   => ! [X,Y] : implies(X,Y) = not(and(X,not(Y))) ) ).

fof(op_implies_or,axiom,
    ( op_implies_or
   => ! [X,Y] : implies(X,Y) = or(not(X),Y) ) ).

fof(op_equiv,axiom,
    ( op_equiv
   => ! [X,Y] : equiv(X,Y) = and(implies(X,Y),implies(Y,X)) ) ).

%------------------------------------------------------------------------------

```

### ./LCL006+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+2 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Hilbert's axiomatization of propositional logic
% Version  : [HB34] axioms.
% English  :

% Refs     : [HB34]  Hilbert & Bernays (1934), Grundlagen der Mathematick
%          : [Hac66] Hackstaff (1966), Systems of Formal Logic
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   18 (  18 unt;   0 def)
%            Number of atoms       :   18 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :   18 (  18 usr;  18 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1
%------------------------------------------------------------------------------
%----Operator definitions to reduce everything to and & not
fof(hilbert_op_or,axiom,
    op_or ).

fof(hilbert_op_implies_and,axiom,
    op_implies_and ).

fof(hilbert_op_equiv,axiom,
    op_equiv ).

%----The one explicit rule
fof(hilbert_modus_ponens,axiom,
    modus_ponens ).

%----The axioms
fof(hilbert_modus_tollens,axiom,
    modus_tollens ).

fof(hilbert_implies_1,axiom,
    implies_1 ).

fof(hilbert_implies_2,axiom,
    implies_2 ).

fof(hilbert_implies_3,axiom,
    implies_3 ).

fof(hilbert_and_1,axiom,
    and_1 ).

fof(hilbert_and_2,axiom,
    and_2 ).

fof(hilbert_and_3,axiom,
    and_3 ).

fof(hilbert_or_1,axiom,
    or_1 ).

fof(hilbert_or_2,axiom,
    or_2 ).

fof(hilbert_or_3,axiom,
    or_3 ).

fof(hilbert_equivalence_1,axiom,
    equivalence_1 ).

fof(hilbert_equivalence_2,axiom,
    equivalence_2 ).

fof(hilbert_equivalence_3,axiom,
    equivalence_3 ).

%----Admissible but not required for completeness. With it much more can
%----be done.
fof(substitution_of_equivalents,axiom,
    substitution_of_equivalents ).

%------------------------------------------------------------------------------

```

### ./LCL006+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+3 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Lukasiewicz's axiomatization of propositional logic
% Version  : [Zem73] axioms.
% English  :

% Refs     : [Zem73] Zeman (1973), Modal Logic, the Lewis-Modal systems
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   8 unt;   0 def)
%            Number of atoms       :    8 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    8 (   8 usr;   8 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1
%------------------------------------------------------------------------------
%----Operator definitions to reduce everything to and & not
fof(luka_op_or,axiom,
    op_or ).

fof(luka_op_implies,axiom,
    op_implies ).

fof(luka_op_equiv,axiom,
    op_equiv ).

%----The one explicit rule
fof(luka_modus_ponens,axiom,
    modus_ponens ).

%----The axioms
fof(luka_cn1,axiom,
    cn1 ).

fof(luka_cn2,axiom,
    cn2 ).

fof(luka_cn3,axiom,
    cn3 ).

%----Admissible but not required for completeness. With it much more can
%----be done.
fof(substitution_of_equivalents,axiom,
    substitution_of_equivalents ).

%------------------------------------------------------------------------------

```

### ./LCL006+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+4 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Principia's axiomatization of propositional logic
% Version  : [RW10] axioms.
% English  :

% Refs     : [RW10]  Russell & Whitehead (1910), Principia Mathmatica
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   10 (  10 unt;   0 def)
%            Number of atoms       :   10 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :   10 (  10 usr;  10 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1
%------------------------------------------------------------------------------
%----Operator definitions to reduce everything to and & not
fof(principia_op_implies_or,axiom,
    op_implies_or ).

fof(principia_op_and,axiom,
    op_and ).

fof(principia_op_equiv,axiom,
    op_equiv ).

%----The one explicit rule
fof(principia_modus_ponens,axiom,
    modus_ponens ).

%----The axioms
fof(principia_r1,axiom,
    r1 ).

fof(principia_r2,axiom,
    r2 ).

fof(principia_r3,axiom,
    r3 ).

%----This is the redundant axiom in Principia
fof(principia_r4,axiom,
    r4 ).

fof(principia_r5,axiom,
    r5 ).

%----Admissible but not required for completeness. With it much more can
%----be done.
fof(substitution_of_equivalents,axiom,
    substitution_of_equivalents ).

%------------------------------------------------------------------------------

```

### ./LCL006+5.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL006+5 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional)
% Axioms   : Rosser's axiomatization of propositional logic
% Version  : [Zem73] axioms.
% English  :

% Refs     : [Zem73] Zeman (1973), Modal Logic, the Lewis-Modal systems
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   8 unt;   0 def)
%            Number of atoms       :    8 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    8 (   8 usr;   8 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1
%------------------------------------------------------------------------------
%----Operator definitions to reduce everything to and & not
fof(rosser_op_or,axiom,
    op_or ).

fof(rosser_op_implies_and,axiom,
    op_implies_and ).

fof(rosser_op_equiv,axiom,
    op_equiv ).

%----The one explicit rule
fof(rosser_modus_ponens,axiom,
    modus_ponens ).

%----The axioms
fof(rosser_kn1,axiom,
    kn1 ).

fof(rosser_kn2,axiom,
    kn2 ).

fof(rosser_kn3,axiom,
    kn3 ).

%----Admissible but not required for completeness. With it much more can
%----be done.
fof(substitution_of_equivalents,axiom,
    substitution_of_equivalents ).

%------------------------------------------------------------------------------

```

### ./LCL007+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+0 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : Propositional modal logic rules and axioms
% Version  : [She06] axioms.
% English  :

% Refs     : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [She06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   23 (   0 unt;   0 def)
%            Number of atoms       :   52 (   1 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   29 (   0   ~;   0   |;   2   &)
%                                         (  23 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   4 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :   25 (  24 usr;  23 prp; 0-2 aty)
%            Number of functors    :    7 (   7 usr;   0 con; 1-2 aty)
%            Number of variables   :   39 (  39   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Rules
fof(necessitation,axiom,
    ( necessitation
  <=> ! [X] :
        ( is_a_theorem(X)
       => is_a_theorem(necessarily(X)) ) ) ).

fof(modus_ponens_strict_implies,axiom,
    ( modus_ponens_strict_implies
  <=> ! [X,Y] :
        ( ( is_a_theorem(X)
          & is_a_theorem(strict_implies(X,Y)) )
       => is_a_theorem(Y) ) ) ).

fof(adjunction,axiom,
    ( adjunction
  <=> ! [X,Y] :
        ( ( is_a_theorem(X)
          & is_a_theorem(Y) )
       => is_a_theorem(and(X,Y)) ) ) ).

fof(substitution_strict_equiv,axiom,
    ( substitution_strict_equiv
  <=> ! [X,Y] :
        ( is_a_theorem(strict_equiv(X,Y))
       => X = Y ) ) ).

%----"Standard" modal axioms
fof(axiom_K,axiom,
    ( axiom_K
  <=> ! [X,Y] : is_a_theorem(implies(necessarily(implies(X,Y)),implies(necessarily(X),necessarily(Y)))) ) ).

fof(axiom_M,axiom,
    ( axiom_M
  <=> ! [X] : is_a_theorem(implies(necessarily(X),X)) ) ).

fof(axiom_4,axiom,
    ( axiom_4
  <=> ! [X] : is_a_theorem(implies(necessarily(X),necessarily(necessarily(X)))) ) ).

fof(axiom_B,axiom,
    ( axiom_B
  <=> ! [X] : is_a_theorem(implies(X,necessarily(possibly(X)))) ) ).

fof(axiom_5,axiom,
    ( axiom_5
  <=> ! [X] : is_a_theorem(implies(possibly(X),necessarily(possibly(X)))) ) ).

%----Axioms for Lewis systems
fof(axiom_s1,axiom,
    ( axiom_s1
  <=> ! [X,Y,Z] : is_a_theorem(implies(and(necessarily(implies(X,Y)),necessarily(implies(Y,Z))),necessarily(implies(X,Z)))) ) ).

fof(axiom_s2,axiom,
    ( axiom_s2
  <=> ! [P,Q] : is_a_theorem(strict_implies(possibly(and(P,Q)),and(possibly(P),possibly(Q)))) ) ).

fof(axiom_s3,axiom,
    ( axiom_s3
  <=> ! [X,Y] : is_a_theorem(strict_implies(strict_implies(X,Y),strict_implies(not(possibly(Y)),not(possibly(X))))) ) ).

fof(axiom_s4,axiom,
    ( axiom_s4
  <=> ! [X] : is_a_theorem(strict_implies(necessarily(X),necessarily(necessarily(X)))) ) ).

%----Axioms for S1-0
fof(axiom_m1,axiom,
    ( axiom_m1
  <=> ! [X,Y] : is_a_theorem(strict_implies(and(X,Y),and(Y,X))) ) ).

fof(axiom_m2,axiom,
    ( axiom_m2
  <=> ! [X,Y] : is_a_theorem(strict_implies(and(X,Y),X)) ) ).

fof(axiom_m3,axiom,
    ( axiom_m3
  <=> ! [X,Y,Z] : is_a_theorem(strict_implies(and(and(X,Y),Z),and(X,and(Y,Z)))) ) ).

fof(axiom_m4,axiom,
    ( axiom_m4
  <=> ! [X] : is_a_theorem(strict_implies(X,and(X,X))) ) ).

fof(axiom_m5,axiom,
    ( axiom_m5
  <=> ! [X,Y,Z] : is_a_theorem(strict_implies(and(strict_implies(X,Y),strict_implies(Y,Z)),strict_implies(X,Z))) ) ).

%----Axioms for building from S1-0
fof(axiom_m6,axiom,
    ( axiom_m6
  <=> ! [X] : is_a_theorem(strict_implies(X,possibly(X))) ) ).

fof(axiom_m7,axiom,
    ( axiom_m7
  <=> ! [P,Q] : is_a_theorem(strict_implies(possibly(and(P,Q)),P)) ) ).

fof(axiom_m8,axiom,
    ( axiom_m8
  <=> ! [P,Q] : is_a_theorem(strict_implies(strict_implies(P,Q),strict_implies(possibly(P),possibly(Q)))) ) ).

fof(axiom_m9,axiom,
    ( axiom_m9
  <=> ! [X] : is_a_theorem(strict_implies(possibly(possibly(X)),possibly(X))) ) ).

fof(axiom_m10,axiom,
    ( axiom_m10
  <=> ! [X] : is_a_theorem(strict_implies(possibly(X),necessarily(possibly(X)))) ) ).

%------------------------------------------------------------------------------

```

### ./LCL007+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+1 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : Propositional modal logic definitions
% Version  : [She06] axioms.
% English  :

% Refs     : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [She06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   0 unt;   0 def)
%            Number of atoms       :    8 (   4 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   4 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    5 (   4 usr;   4 prp; 0-2 aty)
%            Number of functors    :    7 (   7 usr;   0 con; 1-2 aty)
%            Number of variables   :    6 (   6   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Definitions
fof(op_possibly,axiom,
    ( op_possibly
   => ! [X] : possibly(X) = not(necessarily(not(X))) ) ).

fof(op_necessarily,axiom,
    ( op_necessarily
   => ! [X] : necessarily(X) = not(possibly(not(X))) ) ).

fof(op_strict_implies,axiom,
    ( op_strict_implies
   => ! [X,Y] : strict_implies(X,Y) = necessarily(implies(X,Y)) ) ).

fof(op_strict_equiv,axiom,
    ( op_strict_equiv
   => ! [X,Y] : strict_equiv(X,Y) = and(strict_implies(X,Y),strict_implies(Y,X)) ) ).

%------------------------------------------------------------------------------

```

### ./LCL007+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+2 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : KM5 axiomatization of S5 based on Hilbert's PC
% Version  : [HC96] axioms.
% English  :

% Refs     : [HC96]  Hughes & Cresswell (1996), A New Introduction to Modal
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   5 unt;   0 def)
%            Number of atoms       :    5 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    5 (   5 usr;   5 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1, LCL006+2 LCL007+0 LCL007+1
%------------------------------------------------------------------------------
%----Modal definitions
fof(km5_op_possibly,axiom,
    op_possibly ).

%----Modal rules
fof(km5_necessitation,axiom,
    necessitation ).

%----Modal axioms
fof(km5_axiom_K,axiom,
    axiom_K ).

fof(km5_axiom_M,axiom,
    axiom_M ).

fof(km5_axiom_5,axiom,
    axiom_5 ).

%------------------------------------------------------------------------------

```

### ./LCL007+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+3 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : KM4B axiomatization of S5 based on Hilbert's PC
% Version  : [HC96] axioms.
% English  :

% Refs     : [HC96]  Hughes & Cresswell (1996), A New Introduction to Modal
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   6 unt;   0 def)
%            Number of atoms       :    6 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    6 (   6 usr;   6 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+0, LCL006+1, LCL006+2 LCL007+0 LCL007+1
%------------------------------------------------------------------------------
%----Modal definitions
fof(km4b_op_possibly,axiom,
    op_possibly ).

%----Modal rules
fof(km4b_necessitation,axiom,
    necessitation ).

%----Modal axioms
fof(km4b_axiom_K,axiom,
    axiom_K ).

fof(km4b_axiom_M,axiom,
    axiom_M ).

fof(km4b_axiom_4,axiom,
    axiom_4 ).

fof(km4b_axiom_B,axiom,
    axiom_B ).

%------------------------------------------------------------------------------

```

### ./LCL007+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+4 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : Axiomatization of S1-0
% Version  : [Fey50] axioms.
% English  :

% Refs     : [Fey50] Feys (1950), Les systemes formalises de modalites aris
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   14 (  14 unt;   0 def)
%            Number of atoms       :   14 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :   14 (  14 usr;  14 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+1, LCL007+0, LCL007+1
%------------------------------------------------------------------------------
%----Modal definitions
fof(s1_0_op_possibly,axiom,
    op_possibly ).

fof(s1_0_op_or,axiom,
    op_or ).

fof(s1_0_op_implies,axiom,
    op_implies ).

fof(s1_0_op_strict_implies,axiom,
    op_strict_implies ).

fof(s1_0_op_equiv,axiom,
    op_equiv ).

fof(s1_0_op_strict_equiv,axiom,
    op_strict_equiv ).

%----Modal rules
fof(s1_0_modus_ponens_strict_implies,axiom,
    modus_ponens_strict_implies ).

fof(s1_0_substitution_strict_equiv,axiom,
    substitution_strict_equiv ).

fof(s1_0_adjunction,axiom,
    adjunction ).

%----Modal axioms
fof(s1_0_axiom_m1,axiom,
    axiom_m1 ).

fof(s1_0_axiom_m2,axiom,
    axiom_m2 ).

fof(s1_0_axiom_m3,axiom,
    axiom_m3 ).

fof(s1_0_axiom_m4,axiom,
    axiom_m4 ).

fof(s1_0_axiom_m5,axiom,
    axiom_m5 ).

%------------------------------------------------------------------------------

```

### ./LCL007+5.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+5 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : M6S3M9B axiomatization of S5 based on S1-0
% Version  : [Zem73] axioms.
% English  :

% Refs     : [Zem73] Zeman (1973), Modal Logic, the Lewis-Modal systems
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   4 unt;   0 def)
%            Number of atoms       :    4 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    4 (   4 usr;   4 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+1, LCL007+0, LCL007+1, LCL007+4.ax
%------------------------------------------------------------------------------
%----Modal axioms
fof(s1_0_m6s3m9b_axiom_m6,axiom,
    axiom_m6 ).

fof(s1_0_m6s3m9b_axiom_s3,axiom,
    axiom_s3 ).

fof(s1_0_m6s3m9b_axiom_m9,axiom,
    axiom_m9 ).

fof(s1_0_m6s3m9b_axiom_b,axiom,
    axiom_b ).

%------------------------------------------------------------------------------

```

### ./LCL007+6.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL007+6 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Logic Calculi (Propositional modal)
% Axioms   : M10 axiomatization of S5 based on S1-0
% Version  : [Zem73] axioms.
% English  :

% Refs     : [Zem73] Zeman (1973), Modal Logic, the Lewis-Modal systems
%          : [Hal]   Halleck (URL), John Halleck's Logic Systems
%          : [She06] Shen (2006), Automated Proofs of Equivalence of Modal
% Source   : [Hal]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    1 (   1 unt;   0 def)
%            Number of atoms       :    1 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    1 (   1 usr;   1 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments : Requires LCL006+1, LCL007+0, LCL007+1, LCL007+4.ax
%------------------------------------------------------------------------------
%----Modal axioms
fof(s1_0_m10_axiom_m10,axiom,
    axiom_m10 ).

%------------------------------------------------------------------------------

```

### ./LCL008^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL008^0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Logical Calculi (Modal Logic)
% Axioms   : Multi-Modal Logic
% Version  : [Ben08] axioms : Especial.
% English  :

% Refs     : [Ben08] Benzmueller (2008), Email to G. Sutcliffe
%          : [BP08]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben08]
% Names    : MODAL_LOGIC [Ben08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   35 (  15 unt;  20 typ;  15 def)
%            Number of atoms       :   37 (  15 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   35 (   3   ~;   1   |;   2   &;  28   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  28 nst)
%            Number of types       :    3 (   1 usr)
%            Number of type conns  :   79 (  79   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   22 (  19 usr;   3 con; 0-3 aty)
%            Number of variables   :   36 (  28   ^   4   !;   4   ?;  36   :)
% SPC      : 

% Comments : THF0 syntax
%------------------------------------------------------------------------------
%----Our possible worlds are are encoded as terms the type  $i;
%----Here is a constant for the current world:
thf(current_world,type,
    current_world: $i ).

%----Modal logic propositions are then becoming predicates of type ( $i> $o);
%----We introduce some atomic multi-modal logic propositions as constants of
%----type ( $i> $o):
thf(prop_a,type,
    prop_a: $i > $o ).

thf(prop_b,type,
    prop_b: $i > $o ).

thf(prop_c,type,
    prop_c: $i > $o ).

%----The idea is that an atomic multi-modal logic proposition P (of type
%---- $i >  $o) holds at a world W (of type  $i) iff W is in P resp. (P @ W)
%----Now we define the multi-modal logic connectives by reducing them to set
%----operations
%----mfalse corresponds to emptyset (of type $i)
thf(mfalse_decl,type,
    mfalse: $i > $o ).

thf(mfalse,definition,
    ( mfalse
    = ( ^ [X: $i] : $false ) ) ).

%----mtrue corresponds to the universal set (of type $i)
thf(mtrue_decl,type,
    mtrue: $i > $o ).

thf(mtrue,definition,
    ( mtrue
    = ( ^ [X: $i] : $true ) ) ).

%----mnot corresponds to set complement
thf(mnot_decl,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [X: $i > $o,U: $i] :
          ~ ( X @ U ) ) ) ).

%----mor corresponds to set union
thf(mor_decl,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

%----mand corresponds to set intersection
thf(mand_decl,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

%----mimpl defined via mnot and mor
thf(mimpl_decl,type,
    mimpl: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimpl,definition,
    ( mimpl
    = ( ^ [U: $i > $o,V: $i > $o] : ( mor @ ( mnot @ U ) @ V ) ) ) ).

%----miff defined via mand and mimpl
thf(miff_decl,type,
    miff: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(miff,definition,
    ( miff
    = ( ^ [U: $i > $o,V: $i > $o] : ( mand @ ( mimpl @ U @ V ) @ ( mimpl @ V @ U ) ) ) ) ).

%----mbox
thf(mbox_decl,type,
    mbox: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mbox,definition,
    ( mbox
    = ( ^ [R: $i > $i > $o,P: $i > $o,X: $i] :
        ! [Y: $i] :
          ( ( R @ X @ Y )
         => ( P @ Y ) ) ) ) ).

%----mdia
thf(mdia_decl,type,
    mdia: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mdia,definition,
    ( mdia
    = ( ^ [R: $i > $i > $o,P: $i > $o,X: $i] :
        ? [Y: $i] :
          ( ( R @ X @ Y )
          & ( P @ Y ) ) ) ) ).

%----For mall and mexists, i.e., first order modal logic, we declare a new
%----base type individuals
thf(individuals_decl,type,
    individuals: $tType ).

%----mall
thf(mall_decl,type,
    mall: ( individuals > $i > $o ) > $i > $o ).

thf(mall,definition,
    ( mall
    = ( ^ [P: individuals > $i > $o,W: $i] :
        ! [X: individuals] : ( P @ X @ W ) ) ) ).

%----mexists
thf(mexists_decl,type,
    mexists: ( individuals > $i > $o ) > $i > $o ).

thf(mexists,definition,
    ( mexists
    = ( ^ [P: individuals > $i > $o,W: $i] :
        ? [X: individuals] : ( P @ X @ W ) ) ) ).

%----Validity of a multi modal logic formula can now be encoded as
thf(mvalid_decl,type,
    mvalid: ( $i > $o ) > $o ).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [P: $i > $o] :
        ! [W: $i] : ( P @ W ) ) ) ).

%----Satisfiability of a multi modal logic formula can now be encoded as
thf(msatisfiable_decl,type,
    msatisfiable: ( $i > $o ) > $o ).

thf(msatisfiable,definition,
    ( msatisfiable
    = ( ^ [P: $i > $o] :
        ? [W: $i] : ( P @ W ) ) ) ).

%----Countersatisfiability of a multi modal logic formula can now be encoded as
thf(mcountersatisfiable_decl,type,
    mcountersatisfiable: ( $i > $o ) > $o ).

thf(mcountersatisfiable,definition,
    ( mcountersatisfiable
    = ( ^ [P: $i > $o] :
        ? [W: $i] :
          ~ ( P @ W ) ) ) ).

%----Invalidity of a multi modal logic formula can now be encoded as
thf(minvalid_decl,type,
    minvalid: ( $i > $o ) > $o ).

thf(minvalid,definition,
    ( minvalid
    = ( ^ [P: $i > $o] :
        ! [W: $i] :
          ~ ( P @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL009^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL009^0 : TPTP v8.2.0. Released v3.7.0.
% Domain   : Logical Calculi (Modal Logic)
% Axioms   : Translating constructive S4 (CS4) to bimodal classical S4 (BS4)
% Version  : [AM+01] axioms.
% English  :

% Refs     : [AM+01] Alechina et al. (2001), Categorical and Kripke Semanti
%          : [Gar09] Garg (2009), Email to Geoff Sutcliffe
% Source   : [Gar09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   25 (   9 unt;  11 typ;   9 def)
%            Number of atoms       :   69 (   9 equ;   0 cnn)
%            Maximal formula atoms :   10 (   2 avg)
%            Number of connectives :   57 (   0   ~;   0   |;   0   &;  57   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   3 avg;  57 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   49 (  49   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   21 (  20 usr;   9 con; 0-3 aty)
%            Number of variables   :   15 (  10   ^   5   !;   0   ?;  15   :)
% SPC      : 

% Comments : Requires LCL008^0.ax
%          : THF0 syntax
%------------------------------------------------------------------------------
%----To encode constructive S4 into bimodal classical S4, we need two relations
%----reli to encode intuitionistic accessibility, and relr to encode modal
%----accessibility.
thf(reli,type,
    reli: $i > $i > $o ).

thf(relr,type,
    relr: $i > $i > $o ).

%----We now introduce one predicate for each connective of CS4, and define the
%----predicates following [AM+01].
thf(cs4_atom_decl,type,
    cs4_atom: ( $i > $o ) > $i > $o ).

thf(cs4_and_decl,type,
    cs4_and: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(cs4_or_decl,type,
    cs4_or: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(cs4_impl_decl,type,
    cs4_impl: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(cs4_true_decl,type,
    cs4_true: $i > $o ).

thf(cs4_false_decl,type,
    cs4_false: $i > $o ).

thf(cs4_all_decl,type,
    cs4_all: ( individuals > $i > $o ) > $i > $o ).

thf(cs4_box_decl,type,
    cs4_box: ( $i > $o ) > $i > $o ).

thf(cs4_atom,definition,
    ( cs4_atom
    = ( ^ [P: $i > $o] : ( mbox @ reli @ P ) ) ) ).

thf(cs4_and,definition,
    ( cs4_and
    = ( ^ [A: $i > $o,B: $i > $o] : ( mand @ A @ B ) ) ) ).

thf(cs4_or,definition,
    ( cs4_or
    = ( ^ [A: $i > $o,B: $i > $o] : ( mor @ A @ B ) ) ) ).

thf(cs4_impl,definition,
    ( cs4_impl
    = ( ^ [A: $i > $o,B: $i > $o] : ( mbox @ reli @ ( mimpl @ A @ B ) ) ) ) ).

thf(cs4_true,definition,
    cs4_true = mtrue ).

thf(cs4_false,definition,
    cs4_false = mfalse ).

thf(cs4_all,definition,
    ( cs4_all
    = ( ^ [A: individuals > $i > $o] : ( mbox @ reli @ ( mall @ A ) ) ) ) ).

thf(cs4_box,definition,
    ( cs4_box
    = ( ^ [A: $i > $o] : ( mbox @ reli @ ( mbox @ relr @ A ) ) ) ) ).

%----Validity in CS4
thf(cs4_valid_decl,type,
    cs4_valid: ( $i > $o ) > $o ).

thf(cs4_valid_def,definition,
    ( cs4_valid
    = ( ^ [A: $i > $o] : ( mvalid @ A ) ) ) ).

%----Axioms to make the bimodal logic S4xS4.
thf(refl_axiom_i,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ reli @ A ) @ A ) ) ).

thf(refl_axiom_r,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ relr @ A ) @ A ) ) ).

thf(trans_axiom_i,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ reli @ A ) @ ( mbox @ reli @ ( mbox @ reli @ A ) ) ) ) ).

thf(trans_axiom_r,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ relr @ A ) @ ( mbox @ relr @ ( mbox @ relr @ A ) ) ) ) ).

%----Finally, we need a commutativity axiom to recover the axiom 4 in the
%----translation. We need: [i][r] A --> [r][i] A.
thf(ax_i_r_commute,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ reli @ ( mbox @ relr @ A ) ) @ ( mbox @ relr @ ( mbox @ reli @ A ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL010^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL010^0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi
% Axioms   : Propositional intuitionistic logic in HOL
% Version  : [Goe33] axioms.
% English  : An embedding of propositional intuitionisitc logic in HOL based
%            on Goedel's first translation of propositional intuitionistic 
%            logic to modal logic S4.

% Refs     : [Goe33] Goedel (1933), An Interpretation of the Intuitionistic
%          : [Gol06] Goldblatt (2006), Mathematical Modal Logic: A View of
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
%          : [BP10]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben09] 
% Names    : IL2HOL_1 [Ben09]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   41 (  20 unt;  20 typ;  19 def)
%            Number of atoms       :   63 (  19 equ;   0 cnn)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   55 (   3   ~;   1   |;   2   &;  47   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   1 avg;  47 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   95 (  95   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   22 (  20 usr;   1 con; 0-3 aty)
%            Number of variables   :   40 (  31   ^   7   !;   2   ?;  40   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Modal Logic S4 in HOL
%----We define an accessibility relation irel
thf(irel_type,type,
    irel: $i > $i > $o ).

%----We require reflexivity and transitivity for irel
thf(refl_axiom,axiom,
    ! [X: $i] : ( irel @ X @ X ) ).

thf(trans_axiom,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( ( ( irel @ X @ Y )
        & ( irel @ Y @ Z ) )
     => ( irel @ X @ Z ) ) ).

%----We define S4 connective mnot (as set complement)
thf(mnot_decl_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [X: $i > $o,U: $i] :
          ~ ( X @ U ) ) ) ).

%----We define S4 connective mor (as set union) 
thf(mor_decl_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

%----We define S4 connective mand (as set intersection) 
thf(mand_decl_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

%----We define S4 connective mimpl 
thf(mimplies_decl_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [U: $i > $o,V: $i > $o] : ( mor @ ( mnot @ U ) @ V ) ) ) ).

%----Definition of mbox_s4; since irel is reflexive and transitive, 
%----it is easy to show that the K and the T axiom hold for mbox_s4
thf(mbox_s4_decl_type,type,
    mbox_s4: ( $i > $o ) > $i > $o ).

thf(mbox_s4,definition,
    ( mbox_s4
    = ( ^ [P: $i > $o,X: $i] :
        ! [Y: $i] :
          ( ( irel @ X @ Y )
         => ( P @ Y ) ) ) ) ).

%----Intuitionistic Logic in Modal Logic S4
%----Definition of iatom: iatom P = P
%----Goedel maps atoms to atoms
thf(iatom_type,type,
    iatom: ( $i > $o ) > $i > $o ).

thf(iatom,definition,
    ( iatom
    = ( ^ [P: $i > $o] : P ) ) ).

%----Definition of inot: inot P = mnot (mbox_s4 P) 
thf(inot_type,type,
    inot: ( $i > $o ) > $i > $o ).

thf(inot,definition,
    ( inot
    = ( ^ [P: $i > $o] : ( mnot @ ( mbox_s4 @ P ) ) ) ) ).

%----Definition of true and false
thf(itrue_type,type,
    itrue: $i > $o ).

thf(itrue,definition,
    ( itrue
    = ( ^ [W: $i] : $true ) ) ).

thf(ifalse_type,type,
    ifalse: $i > $o ).

thf(ifalse,definition,
    ( ifalse
    = ( inot @ itrue ) ) ).

%----Definition of iand: iand P Q = (mand P Q)
thf(iand_type,type,
    iand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iand,definition,
    ( iand
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mand @ P @ Q ) ) ) ).

%----Definition of ior: ior P Q = (mor (mbox_s4 P) (mbox_s4 Q))
thf(ior_type,type,
    ior: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ior,definition,
    ( ior
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mor @ ( mbox_s4 @ P ) @ ( mbox_s4 @ Q ) ) ) ) ).

%----Definition of iimplies: iimplies P Q = 
%---- (mimplies (mbox_s4 P) (mbox_s4 Q))
thf(iimplies_type,type,
    iimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplies,definition,
    ( iimplies
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mimplies @ ( mbox_s4 @ P ) @ ( mbox_s4 @ Q ) ) ) ) ).

%----Definition of iimplied: iimplied P Q = (iimplies Q P)
thf(iimplied_type,type,
    iimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplied,definition,
    ( iimplied
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iimplies @ Q @ P ) ) ) ).

%----Definition of iequiv: iequiv P Q = 
%---- (iand (iimplies P Q) (iimplies Q P))
thf(iequiv_type,type,
    iequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iequiv,definition,
    ( iequiv
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iand @ ( iimplies @ P @ Q ) @ ( iimplies @ Q @ P ) ) ) ) ).

%----Definition of ixor: ixor P Q = (inot (iequiv P Q)
thf(ixor_type,type,
    ixor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ixor,definition,
    ( ixor
    = ( ^ [P: $i > $o,Q: $i > $o] : ( inot @ ( iequiv @ P @ Q ) ) ) ) ).

%----Definition of validity
thf(ivalid_type,type,
    ivalid: ( $i > $o ) > $o ).

thf(ivalid,definition,
    ( ivalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of satisfiability
thf(isatisfiable_type,type,
    isatisfiable: ( $i > $o ) > $o ).

thf(isatisfiable,definition,
    ( isatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of countersatisfiability
thf(icountersatisfiable_type,type,
    icountersatisfiable: ( $i > $o ) > $o ).

thf(icountersatisfiable,definition,
    ( icountersatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(iinvalid_type,type,
    iinvalid: ( $i > $o ) > $o ).

thf(iinvalid,definition,
    ( iinvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL011^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL011^0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi
% Axioms   : Propositional intuitionistic logic in HOL
% Version  : [Goe33] axioms.
% English  : An embedding of propositional intuitionisitc logic in HOL based
%            on Goedel's second translation of propositional intuitionistic 
%            logic to modal logic S4.

% Refs     : [Goe33] Goedel (1933), An Interpretation of the Intuitionistic
%          : [Gol06] Goldblatt (2006), Mathematical Modal Logic: A View of
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
%          : [BP10]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben09]
% Names    : IL2HOL_2 [Ben09]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   41 (  20 unt;  20 typ;  19 def)
%            Number of atoms       :   65 (  19 equ;   0 cnn)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   57 (   3   ~;   1   |;   2   &;  49   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   1 avg;  49 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   95 (  95   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   22 (  20 usr;   1 con; 0-3 aty)
%            Number of variables   :   40 (  31   ^   7   !;   2   ?;  40   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Modal Logic S4 in HOL
%----We define an accessibility relation irel
thf(irel_type,type,
    irel: $i > $i > $o ).

%----We require reflexivity and transitivity for irel
thf(refl_axiom,axiom,
    ! [X: $i] : ( irel @ X @ X ) ).

thf(trans_axiom,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( ( ( irel @ X @ Y )
        & ( irel @ Y @ Z ) )
     => ( irel @ X @ Z ) ) ).

%----We define S4 connective mnot (as set complement)
thf(mnot_decl_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [X: $i > $o,U: $i] :
          ~ ( X @ U ) ) ) ).

%----We define S4 connective mor (as set union) 
thf(mor_decl_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

%----We define S4 connective mand (as set intersection) 
thf(mand_decl_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

%----We define S4 connective mimpl 
thf(mimplies_decl_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [U: $i > $o,V: $i > $o] : ( mor @ ( mnot @ U ) @ V ) ) ) ).

%----Definition of mbox_s4; since irel is reflexive and transitive, 
%----it is easy to show that the K and the T axiom hold for mbox_s4
thf(mbox_s4_decl_type,type,
    mbox_s4: ( $i > $o ) > $i > $o ).

thf(mbox_s4,definition,
    ( mbox_s4
    = ( ^ [P: $i > $o,X: $i] :
        ! [Y: $i] :
          ( ( irel @ X @ Y )
         => ( P @ Y ) ) ) ) ).

%----Intuitionistic Logic in Modal Logic S4
%----Definition of iatom: iatom P = P
%----Goedel maps atoms to atoms
thf(iatom_type,type,
    iatom: ( $i > $o ) > $i > $o ).

thf(iatom,definition,
    ( iatom
    = ( ^ [P: $i > $o] : P ) ) ).

%----Definition of inot: inot P = (mbox_s4 (mnot (mbox_s4 P)))
thf(inot_type,type,
    inot: ( $i > $o ) > $i > $o ).

thf(inot,definition,
    ( inot
    = ( ^ [P: $i > $o] : ( mnot @ ( mbox_s4 @ P ) ) ) ) ).

%----Definition of true and false
thf(itrue_type,type,
    itrue: $i > $o ).

thf(itrue,definition,
    ( itrue
    = ( ^ [W: $i] : $true ) ) ).

thf(ifalse_type,type,
    ifalse: $i > $o ).

thf(ifalse,definition,
    ( ifalse
    = ( inot @ itrue ) ) ).

%----Definition of iand: iand P Q = (mand (mbox_s4 P) (mbox_s4 Q)) 
thf(iand_type,type,
    iand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iand,definition,
    ( iand
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mand @ ( mbox_s4 @ P ) @ ( mbox_s4 @ Q ) ) ) ) ).

%---- Definition of ior: ior P Q = (mor (mbox_s4 P) (mbox_s4 Q))
thf(ior_type,type,
    ior: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ior,definition,
    ( ior
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mor @ ( mbox_s4 @ P ) @ ( mbox_s4 @ Q ) ) ) ) ).

%----Definition of iimplies: iimplies P Q = 
%---- (mimplies (mbox_s4 P) (mbox_s4 Q))
thf(iimplies_type,type,
    iimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplies,definition,
    ( iimplies
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mimplies @ ( mbox_s4 @ P ) @ ( mbox_s4 @ Q ) ) ) ) ).

%----Definition of iimplied: iimplied P Q = (iimplies Q P)
thf(iimplied_type,type,
    iimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplied,definition,
    ( iimplied
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iimplies @ Q @ P ) ) ) ).

%----Definition of iequiv: iequiv P Q = 
%---- (iand (iimplies P Q) (iimplies Q P))
thf(iequiv_type,type,
    iequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iequiv,definition,
    ( iequiv
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iand @ ( iimplies @ P @ Q ) @ ( iimplies @ Q @ P ) ) ) ) ).

%----Definition of ixor: ixor P Q = (inot (iequiv P Q)
thf(ixor_type,type,
    ixor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ixor,definition,
    ( ixor
    = ( ^ [P: $i > $o,Q: $i > $o] : ( inot @ ( iequiv @ P @ Q ) ) ) ) ).

%----Definition of validity
thf(ivalid_type,type,
    ivalid: ( $i > $o ) > $o ).

thf(ivalid,definition,
    ( ivalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of satisfiability
thf(isatisfiable_type,type,
    isatisfiable: ( $i > $o ) > $o ).

thf(isatisfiable,definition,
    ( isatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of countersatisfiability
thf(icountersatisfiable_type,type,
    icountersatisfiable: ( $i > $o ) > $o ).

thf(icountersatisfiable,definition,
    ( icountersatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(iinvalid_type,type,
    iinvalid: ( $i > $o ) > $o ).

thf(iinvalid,definition,
    ( iinvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL012^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL012^0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi
% Axioms   : Propositional intuitionistic logic in HOL
% Version  : [MT48] axioms.
% English  : An embedding of propositional intuitionisitc logic in HOL based
%            on the McKinsey/Tarski translation of propositional intuitionistic
%            logic to modal logic S4.

% Refs     : [MT48]  McKinsey & Tarski (1948), Some Theorems about the Sent
%          : [Gol06] Goldblatt (2006), Mathematical Modal Logic: A View of
%          : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
%          : [BP10]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben09]
% Names    : IL2HOL_3 [Ben09]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   41 (  20 unt;  20 typ;  19 def)
%            Number of atoms       :   61 (  19 equ;   0 cnn)
%            Maximal formula atoms :    3 (   1 avg)
%            Number of connectives :   53 (   3   ~;   1   |;   2   &;  45   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   1 avg;  45 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   95 (  95   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   22 (  20 usr;   1 con; 0-3 aty)
%            Number of variables   :   40 (  31   ^   7   !;   2   ?;  40   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Modal Logic S4 in HOL
%----We define an accessibility relation irel
thf(irel_type,type,
    irel: $i > $i > $o ).

%----We require reflexivity and transitivity for irel
thf(refl_axiom,axiom,
    ! [X: $i] : ( irel @ X @ X ) ).

thf(trans_axiom,axiom,
    ! [X: $i,Y: $i,Z: $i] :
      ( ( ( irel @ X @ Y )
        & ( irel @ Y @ Z ) )
     => ( irel @ X @ Z ) ) ).

%----We define S4 connective mnot (as set complement)
thf(mnot_decl_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [X: $i > $o,U: $i] :
          ~ ( X @ U ) ) ) ).

%----We define S4 connective mor (as set union) 
thf(mor_decl_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

%----We define S4 connective mand (as set intersection) 
thf(mand_decl_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

%----We define S4 connective mimpl 
thf(mimplies_decl_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [U: $i > $o,V: $i > $o] : ( mor @ ( mnot @ U ) @ V ) ) ) ).

%----Definition of mbox_s4; since irel is reflexive and transitive, 
%----it is easy to show that the K and the T axiom hold for mbox_s4
thf(mbox_s4_decl_type,type,
    mbox_s4: ( $i > $o ) > $i > $o ).

thf(mbox_s4,definition,
    ( mbox_s4
    = ( ^ [P: $i > $o,X: $i] :
        ! [Y: $i] :
          ( ( irel @ X @ Y )
         => ( P @ Y ) ) ) ) ).

%----Intuitionistic Logic in Modal Logic S4
%----Definition of iatom: iatom P = (mbox_s4 P)
thf(iatom_type,type,
    iatom: ( $i > $o ) > $i > $o ).

thf(iatom,definition,
    ( iatom
    = ( ^ [P: $i > $o] : ( mbox_s4 @ P ) ) ) ).

%----Definition of inot: inot P = (mbox_s4 (mnot P))
thf(inot_type,type,
    inot: ( $i > $o ) > $i > $o ).

thf(inot,definition,
    ( inot
    = ( ^ [P: $i > $o] : ( mbox_s4 @ ( mnot @ P ) ) ) ) ).

%----Definition of true and false
thf(itrue_type,type,
    itrue: $i > $o ).

thf(itrue,definition,
    ( itrue
    = ( ^ [W: $i] : $true ) ) ).

thf(ifalse_type,type,
    ifalse: $i > $o ).

thf(ifalse,definition,
    ( ifalse
    = ( inot @ itrue ) ) ).

%----Definition of iand: iand P Q = (mand P Q)
thf(iand_type,type,
    iand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iand,definition,
    ( iand
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mand @ P @ Q ) ) ) ).

%----Definition of ior: ior P Q = (mor P Q)
thf(ior_type,type,
    ior: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ior,definition,
    ( ior
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mor @ P @ Q ) ) ) ).

%----Definition of iimplies: iimplies P Q = 
%---- (mbox_s4 (mimiplies P Q)
thf(iimplies_type,type,
    iimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplies,definition,
    ( iimplies
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mbox_s4 @ ( mimplies @ P @ Q ) ) ) ) ).

%----Definition of iimplied: iimplied P Q = (iimplies Q P)
thf(iimplied_type,type,
    iimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iimplied,definition,
    ( iimplied
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iimplies @ Q @ P ) ) ) ).

%----Definition of iequiv: iequiv P Q = 
%---- (iand (iimplies P Q) (iimplies Q P))
thf(iequiv_type,type,
    iequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(iequiv,definition,
    ( iequiv
    = ( ^ [P: $i > $o,Q: $i > $o] : ( iand @ ( iimplies @ P @ Q ) @ ( iimplies @ Q @ P ) ) ) ) ).

%----Definition of ixor: ixor P Q = (mnot (iequiv P Q))
thf(ixor_type,type,
    ixor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(ixor,definition,
    ( ixor
    = ( ^ [P: $i > $o,Q: $i > $o] : ( mnot @ ( iequiv @ P @ Q ) ) ) ) ).

%----Definition of validity
thf(ivalid_type,type,
    ivalid: ( $i > $o ) > $o ).

thf(ivalid,definition,
    ( ivalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of satisfiability
thf(isatisfiable_type,type,
    isatisfiable: ( $i > $o ) > $o ).

thf(isatisfiable,definition,
    ( isatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of countersatisfiability
thf(icountersatisfiable_type,type,
    icountersatisfiable: ( $i > $o ) > $o ).

thf(icountersatisfiable,definition,
    ( icountersatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(iinvalid_type,type,
    iinvalid: ( $i > $o ) > $o ).

thf(iinvalid,definition,
    ( iinvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL013^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^0 : TPTP v8.2.0. Bugfixed v5.0.0.
% Domain   : Logic Calculi (Quantified multimodal logic)
% Axioms   : Embedding of quantified multimodal logic in simple type theory
% Version  : [Ben09] axioms.
% English  : 

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :   63 (  31 unt;  32 typ;  31 def)
%            Number of atoms       :   92 (  36 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :  123 (   4   ~;   4   |;   8   &;  99   @)
%                                         (   0 <=>;   8  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  99 nst)
%            Number of types       :    3 (   1 usr)
%            Number of type conns  :  168 ( 168   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   33 (  31 usr;   1 con; 0-3 aty)
%            Number of variables   :   84 (  49   ^  29   !;   6   ?;  84   :)
% SPC      : 

% Comments : 
% Bugfixes : v5.0.0 - Fixed mpartially_functional_type
%------------------------------------------------------------------------------
%----Declaration of additional base type mu
thf(mu_type,type,
    mu: $tType ).

%----Equality
thf(meq_ind_type,type,
    meq_ind: mu > mu > $i > $o ).

thf(meq_ind,definition,
    ( meq_ind
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) ) ).

thf(meq_prop_type,type,
    meq_prop: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(meq_prop,definition,
    ( meq_prop
    = ( ^ [X: $i > $o,Y: $i > $o,W: $i] :
          ( ( X @ W )
          = ( Y @ W ) ) ) ) ).

%----Modal operators not, or, box, Pi 
thf(mnot_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) ) ).

thf(mor_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) ) ).

thf(mand_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mnot @ ( mor @ ( mnot @ Phi ) @ ( mnot @ Psi ) ) ) ) ) ).

thf(mimplies_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mor @ ( mnot @ Phi ) @ Psi ) ) ) ).

thf(mimplied_type,type,
    mimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplied,definition,
    ( mimplied
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mor @ ( mnot @ Psi ) @ Phi ) ) ) ).

thf(mequiv_type,type,
    mequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mequiv,definition,
    ( mequiv
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mand @ ( mimplies @ Phi @ Psi ) @ ( mimplies @ Psi @ Phi ) ) ) ) ).

thf(mxor_type,type,
    mxor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mxor,definition,
    ( mxor
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mnot @ ( mequiv @ Phi @ Psi ) ) ) ) ).

%----Universal quantification: individuals
thf(mforall_ind_type,type,
    mforall_ind: ( mu > $i > $o ) > $i > $o ).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] : ( Phi @ X @ W ) ) ) ).

thf(mforall_prop_type,type,
    mforall_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_prop,definition,
    ( mforall_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ! [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

thf(mexists_ind_type,type,
    mexists_ind: ( mu > $i > $o ) > $i > $o ).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o] :
          ( mnot
          @ ( mforall_ind
            @ ^ [X: mu] : ( mnot @ ( Phi @ X ) ) ) ) ) ) ).

thf(mexists_prop_type,type,
    mexists_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_prop,definition,
    ( mexists_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o] :
          ( mnot
          @ ( mforall_prop
            @ ^ [P: $i > $o] : ( mnot @ ( Phi @ P ) ) ) ) ) ) ).

thf(mtrue_type,type,
    mtrue: $i > $o ).

thf(mtrue,definition,
    ( mtrue
    = ( ^ [W: $i] : $true ) ) ).

thf(mfalse_type,type,
    mfalse: $i > $o ).

thf(mfalse,definition,
    ( mfalse
    = ( mnot @ mtrue ) ) ).

thf(mbox_type,type,
    mbox: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mbox,definition,
    ( mbox
    = ( ^ [R: $i > $i > $o,Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( R @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_type,type,
    mdia: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mdia,definition,
    ( mdia
    = ( ^ [R: $i > $i > $o,Phi: $i > $o] : ( mnot @ ( mbox @ R @ ( mnot @ Phi ) ) ) ) ) ).

%----Definition of properties of accessibility relations
thf(mreflexive_type,type,
    mreflexive: ( $i > $i > $o ) > $o ).

thf(mreflexive,definition,
    ( mreflexive
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] : ( R @ S @ S ) ) ) ).

thf(msymmetric_type,type,
    msymmetric: ( $i > $i > $o ) > $o ).

thf(msymmetric,definition,
    ( msymmetric
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i] :
          ( ( R @ S @ T )
         => ( R @ T @ S ) ) ) ) ).

thf(mserial_type,type,
    mserial: ( $i > $i > $o ) > $o ).

thf(mserial,definition,
    ( mserial
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] :
        ? [T: $i] : ( R @ S @ T ) ) ) ).

thf(mtransitive_type,type,
    mtransitive: ( $i > $i > $o ) > $o ).

thf(mtransitive,definition,
    ( mtransitive
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ T @ U ) )
         => ( R @ S @ U ) ) ) ) ).

thf(meuclidean_type,type,
    meuclidean: ( $i > $i > $o ) > $o ).

thf(meuclidean,definition,
    ( meuclidean
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( R @ T @ U ) ) ) ) ).

thf(mpartially_functional_type,type,
    mpartially_functional: ( $i > $i > $o ) > $o ).

thf(mpartially_functional,definition,
    ( mpartially_functional
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( T = U ) ) ) ) ).

thf(mfunctional_type,type,
    mfunctional: ( $i > $i > $o ) > $o ).

thf(mfunctional,definition,
    ( mfunctional
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] :
        ? [T: $i] :
          ( ( R @ S @ T )
          & ! [U: $i] :
              ( ( R @ S @ U )
             => ( T = U ) ) ) ) ) ).

thf(mweakly_dense_type,type,
    mweakly_dense: ( $i > $i > $o ) > $o ).

thf(mweakly_dense,definition,
    ( mweakly_dense
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( R @ S @ T )
         => ? [U: $i] :
              ( ( R @ S @ U )
              & ( R @ U @ T ) ) ) ) ) ).

thf(mweakly_connected_type,type,
    mweakly_connected: ( $i > $i > $o ) > $o ).

thf(mweakly_connected,definition,
    ( mweakly_connected
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( ( R @ T @ U )
            | ( T = U )
            | ( R @ U @ T ) ) ) ) ) ).

thf(mweakly_directed_type,type,
    mweakly_directed: ( $i > $i > $o ) > $o ).

thf(mweakly_directed,definition,
    ( mweakly_directed
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ? [V: $i] :
              ( ( R @ T @ V )
              & ( R @ U @ V ) ) ) ) ) ).

%----Definition of validity
thf(mvalid_type,type,
    mvalid: ( $i > $o ) > $o ).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(minvalid_type,type,
    minvalid: ( $i > $o ) > $o ).

thf(minvalid,definition,
    ( minvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%----Definition of satisfiability
thf(msatisfiable_type,type,
    msatisfiable: ( $i > $o ) > $o ).

thf(msatisfiable,definition,
    ( msatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of countersatisfiability
thf(mcountersatisfiable_type,type,
    mcountersatisfiable: ( $i > $o ) > $o ).

thf(mcountersatisfiable,definition,
    ( mcountersatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL013^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^1 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic K
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic K in simple type theory.

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :    8 (   2 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    8 (   1   ~;   1   |;   0   &;   6   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;   6 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    5 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_k
thf(rel_k_type,type,
    rel_k: $i > $i > $o ).

%----We define mbox_k and mdia_k based on rel_k
thf(mbox_k_type,type,
    mbox_k: ( $i > $o ) > $i > $o ).

thf(mbox_k,definition,
    ( mbox_k
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_k @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_k_type,type,
    mdia_k: ( $i > $o ) > $i > $o ).

thf(mdia_k,definition,
    ( mdia_k
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_k @ ( mnot @ Phi ) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL013^2.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^2 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic D
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic D in simple type theory

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :   10 (   2 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    9 (   1   ~;   1   |;   0   &;   7   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   1 avg;   7 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    6 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_d
thf(rel_d_type,type,
    rel_d: $i > $i > $o ).

%----We define mbox_d and mdia_d based on rel_d
thf(mbox_d_type,type,
    mbox_d: ( $i > $o ) > $i > $o ).

thf(mbox_d,definition,
    ( mbox_d
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_d @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_d_type,type,
    mdia_d: ( $i > $o ) > $i > $o ).

thf(mdia_d,definition,
    ( mdia_d
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_d @ ( mnot @ Phi ) ) ) ) ) ).

%----We have now two options for stating the B conditions: 
%----We can (i) directly formulate conditions for the accessibility relation
%----constant or we can (ii) state corresponding axioms. We here prefer (i)
thf(a1,axiom,
    mserial @ rel_d ).

%------------------------------------------------------------------------------

```

### ./LCL013^3.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^3 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic M
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic M in simple type theory.

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :   10 (   2 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    9 (   1   ~;   1   |;   0   &;   7   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   1 avg;   7 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    6 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_m
thf(rel_m_type,type,
    rel_m: $i > $i > $o ).

%----We define mbox_m and mdia_m based on rel_m
thf(mbox_m_type,type,
    mbox_m: ( $i > $o ) > $i > $o ).

thf(mbox_m,definition,
    ( mbox_m
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_m @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_m_type,type,
    mdia_m: ( $i > $o ) > $i > $o ).

thf(mdia_m,definition,
    ( mdia_m
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_m @ ( mnot @ Phi ) ) ) ) ) ).

%----We have now two options for stating the B conditions: 
%----We can (i) directly formulate conditions for the accessibility relation
%----constant or we can (ii) state corresponding axioms. We here prefer (i)
thf(a1,axiom,
    mreflexive @ rel_m ).

%------------------------------------------------------------------------------

```

### ./LCL013^4.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^4 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic B
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic B in simple type theory.

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    7 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :   12 (   2 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :   10 (   1   ~;   1   |;   0   &;   8   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg;   8 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    7 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_b
thf(rel_b_type,type,
    rel_b: $i > $i > $o ).

%----We define mbox_b and mdia_b based on rel_b
thf(mbox_b_type,type,
    mbox_b: ( $i > $o ) > $i > $o ).

thf(mbox_b,definition,
    ( mbox_b
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_b @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_b_type,type,
    mdia_b: ( $i > $o ) > $i > $o ).

thf(mdia_b,definition,
    ( mdia_b
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_b @ ( mnot @ Phi ) ) ) ) ) ).

%----We have now two options for stating the B conditions: 
%----We can (i) directly formulate conditions for the accessibility relation
%----constant or we can (ii) state corresponding axioms. We here prefer (i)
thf(a1,axiom,
    mreflexive @ rel_b ).

thf(a2,axiom,
    msymmetric @ rel_b ).

%------------------------------------------------------------------------------

```

### ./LCL013^5.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^5 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic S4
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic S4 in simple type theory.

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    7 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :   12 (   2 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :   10 (   1   ~;   1   |;   0   &;   8   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg;   8 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    7 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0 or (LCL015^0 and LCL015^1)
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_s4
thf(rel_s4_type,type,
    rel_s4: $i > $i > $o ).

%----We define mbox_s4 and mdia_s4 based on rel_s4
thf(mbox_s4_type,type,
    mbox_s4: ( $i > $o ) > $i > $o ).

thf(mbox_s4,definition,
    ( mbox_s4
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_s4 @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_s4_type,type,
    mdia_s4: ( $i > $o ) > $i > $o ).

thf(mdia_s4,definition,
    ( mdia_s4
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_s4 @ ( mnot @ Phi ) ) ) ) ) ).

%----We have now two options for stating the B conditions: 
%----We can (i) directly formulate conditions for the accessibility relation
%----constant or we can (ii) state corresponding axioms. We here prefer (i)
thf(a1,axiom,
    mreflexive @ rel_s4 ).

thf(a2,axiom,
    mtransitive @ rel_s4 ).

%------------------------------------------------------------------------------

```

### ./LCL013^6.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL013^6 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal logic)
% Axioms   : Modal logic S5
% Version  : [Ben09] axioms.
% English  : Embedding of monomodal logic S5 in simple type theory.

% Refs     : [Ben09] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   2 unt;   3 typ;   2 def)
%            Number of atoms       :   14 (   2 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :   11 (   1   ~;   1   |;   0   &;   9   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg;   9 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   10 (  10   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    8 (   7 usr;   4 con; 0-2 aty)
%            Number of variables   :    4 (   3   ^   1   !;   0   ?;   4   :)
% SPC      : 

% Comments : Requires LCL013^0
%------------------------------------------------------------------------------
%----We reserve an accessibility relation constant rel_s5
thf(rel_s5_type,type,
    rel_s5: $i > $i > $o ).

%----We define mbox_s5 and mdia_s5 based on rel_s5
thf(mbox_s5_type,type,
    mbox_s5: ( $i > $o ) > $i > $o ).

thf(mbox_s5,definition,
    ( mbox_s5
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel_s5 @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mdia_s5_type,type,
    mdia_s5: ( $i > $o ) > $i > $o ).

thf(mdia_s5,definition,
    ( mdia_s5
    = ( ^ [Phi: $i > $o] : ( mnot @ ( mbox_s5 @ ( mnot @ Phi ) ) ) ) ) ).

%----We have now two options for stating the B conditions: 
%----We can (i) directly formulate conditions for the accessibility relation
%----constant or we can (ii) state corresponding axioms. We here prefer (i)
thf(a1,axiom,
    mreflexive @ rel_s5 ).

thf(a2,axiom,
    mtransitive @ rel_s5 ).

thf(a3,axiom,
    msymmetric @ rel_s5 ).

%------------------------------------------------------------------------------

```

### ./LCL014^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL014^0 : TPTP v8.2.0. Released .0.
% Domain   : Logical Calculi
% Axioms   : Region Connection Calculus
% Version  : [RCC92] axioms.
% English  : 

% Refs     : [RCC92] Randell et al. (1992), A Spatial Logic Based on Region
%          : [Ben10a] Benzmueller (2010), Email to Geoff Sutcliffe
%          : [Ben10b] Benzmueller (2010), Simple Type Theory as a Framework
% Source   : [Ben10a]
% Names    : RCC.ax [Ben10a]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   22 (  10 unt;  11 typ;   9 def)
%            Number of atoms       :   41 (   9 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :   64 (   6   ~;   0   |;  10   &;  46   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   2 avg;  46 nst)
%            Number of types       :    2 (   1 usr)
%            Number of type conns  :   20 (  20   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   11 (  10 usr;   0 con; 2-2 aty)
%            Number of variables   :   25 (  18   ^   4   !;   3   ?;  25   :)
% SPC      : 

% Comments : 
%------------------------------------------------------------------------------
thf(reg_type,type,
    reg: $tType ).

thf(c_type,type,
    c: reg > reg > $o ).

thf(dc_type,type,
    dc: reg > reg > $o ).

thf(p_type,type,
    p: reg > reg > $o ).

thf(eq_type,type,
    eq: reg > reg > $o ).

thf(o_type,type,
    o: reg > reg > $o ).

thf(po_type,type,
    po: reg > reg > $o ).

thf(ec_type,type,
    ec: reg > reg > $o ).

thf(pp_type,type,
    pp: reg > reg > $o ).

thf(tpp_type,type,
    tpp: reg > reg > $o ).

thf(ntpp_type,type,
    ntpp: reg > reg > $o ).

thf(c_reflexive,axiom,
    ! [X: reg] : ( c @ X @ X ) ).

thf(c_symmetric,axiom,
    ! [X: reg,Y: reg] :
      ( ( c @ X @ Y )
     => ( c @ Y @ X ) ) ).

thf(dc,definition,
    ( dc
    = ( ^ [X: reg,Y: reg] :
          ~ ( c @ X @ Y ) ) ) ).

thf(p,definition,
    ( p
    = ( ^ [X: reg,Y: reg] :
        ! [Z: reg] :
          ( ( c @ Z @ X )
         => ( c @ Z @ Y ) ) ) ) ).

thf(eq,definition,
    ( eq
    = ( ^ [X: reg,Y: reg] :
          ( ( p @ X @ Y )
          & ( p @ Y @ X ) ) ) ) ).

thf(o,definition,
    ( o
    = ( ^ [X: reg,Y: reg] :
        ? [Z: reg] :
          ( ( p @ Z @ X )
          & ( p @ Z @ Y ) ) ) ) ).

thf(po,definition,
    ( po
    = ( ^ [X: reg,Y: reg] :
          ( ( o @ X @ Y )
          & ~ ( p @ X @ Y )
          & ~ ( p @ Y @ X ) ) ) ) ).

thf(ec,definition,
    ( ec
    = ( ^ [X: reg,Y: reg] :
          ( ( c @ X @ Y )
          & ~ ( o @ X @ Y ) ) ) ) ).

thf(pp,definition,
    ( pp
    = ( ^ [X: reg,Y: reg] :
          ( ( p @ X @ Y )
          & ~ ( p @ Y @ X ) ) ) ) ).

thf(tpp,definition,
    ( tpp
    = ( ^ [X: reg,Y: reg] :
          ( ( pp @ X @ Y )
          & ? [Z: reg] :
              ( ( ec @ Z @ X )
              & ( ec @ Z @ Y ) ) ) ) ) ).

thf(ntpp,definition,
    ( ntpp
    = ( ^ [X: reg,Y: reg] :
          ( ( pp @ X @ Y )
          & ~ ? [Z: reg] :
                ( ( ec @ Z @ X )
                & ( ec @ Z @ Y ) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL015^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL015^0 : TPTP v8.2.0. Released v5.5.0.
% Domain   : Logic Calculi (Quantified multimodal logic, cumulative domains)
% Axioms   : Embedding of quantified multimodal logic in simple type theory
% Version  : [Ben12] axioms.
% English  : 

% Refs     : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :   64 (  31 unt;  33 typ;  30 def)
%            Number of atoms       :   91 (  34 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :  128 (   4   ~;   4   |;   8   &; 103   @)
%                                         (   0 <=>;   9  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   1 avg; 103 nst)
%            Number of types       :    3 (   1 usr)
%            Number of type conns  :  170 ( 170   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   34 (  32 usr;   1 con; 0-3 aty)
%            Number of variables   :   83 (  46   ^  30   !;   7   ?;  83   :)
% SPC      : THF_SAT_EQU

% Comments : LCL015^1 and this are essentially LCL013^0.ax with the following 
%            modifications to support cumulative domains:
%            - addition of a predicate exists_in_world
%            - use of this predicate in a modified definition mforall_ind
%            - use of this predicate in an added axiom for cumulative domains
%------------------------------------------------------------------------------
%----Declaration of additional base type mu
thf(mu_type,type,
    mu: $tType ).

%----Equality
thf(qmltpeq_type,type,
    qmltpeq: mu > mu > $i > $o ).

% originale Definition
%thf(qmltpeq,definition,
%    ( qmltpeq
%    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) )).

% erweiterte Leibnitz-Definition
%thf(qmltpeq,definition,
% ( qmltpeq
% = ( ^ [X: mu,Y: mu,W: $i] : (![P: mu > $i > $o]: ( (P @ X @ W) <=> (P @ Y @ W) ) ) ) )).

%  Leibnitz-Definition
%thf(qmltpeq,definition,
% ( qmltpeq
%  = ( ^ [X: mu,Y: mu,W: $i] : (! [P: mu > $o]: ( (P @ X) <=> (P @ Y) ) ) ) )).

thf(meq_prop_type,type,
    meq_prop: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(meq_prop,definition,
    ( meq_prop
    = ( ^ [X: $i > $o,Y: $i > $o,W: $i] :
          ( ( X @ W )
          = ( Y @ W ) ) ) ) ).

%----Modal operators not, or, box, Pi 
thf(mnot_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) ) ).

thf(mor_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) ) ).

thf(mbox_type,type,
    mbox: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mbox,definition,
    ( mbox
    = ( ^ [R: $i > $i > $o,Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( R @ W @ V )
          | ( Phi @ V ) ) ) ) ).

thf(mforall_prop_type,type,
    mforall_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_prop,definition,
    ( mforall_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ! [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

%----Further modal operators
thf(mtrue_type,type,
    mtrue: $i > $o ).

thf(mtrue,definition,
    ( mtrue
    = ( ^ [W: $i] : $true ) ) ).

thf(mfalse_type,type,
    mfalse: $i > $o ).

thf(mfalse,definition,
    ( mfalse
    = ( mnot @ mtrue ) ) ).

thf(mand_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mnot @ ( mor @ ( mnot @ Phi ) @ ( mnot @ Psi ) ) ) ) ) ).

thf(mimplies_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mor @ ( mnot @ Phi ) @ Psi ) ) ) ).

thf(mimplied_type,type,
    mimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplied,definition,
    ( mimplied
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mor @ ( mnot @ Psi ) @ Phi ) ) ) ).

thf(mequiv_type,type,
    mequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mequiv,definition,
    ( mequiv
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mand @ ( mimplies @ Phi @ Psi ) @ ( mimplies @ Psi @ Phi ) ) ) ) ).

thf(mxor_type,type,
    mxor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mxor,definition,
    ( mxor
    = ( ^ [Phi: $i > $o,Psi: $i > $o] : ( mnot @ ( mequiv @ Phi @ Psi ) ) ) ) ).

thf(mdia_type,type,
    mdia: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mdia,definition,
    ( mdia
    = ( ^ [R: $i > $i > $o,Phi: $i > $o] : ( mnot @ ( mbox @ R @ ( mnot @ Phi ) ) ) ) ) ).

%--- (new for cumulative)
%---Declaration of existence predicate for simulating cumulative domain
thf(exists_in_world_type,type,
    exists_in_world: mu > $i > $o ).

%----The domains are non-empty
thf(nonempty_ax,axiom,
    ! [V: $i] :
    ? [X: mu] : ( exists_in_world @ X @ V ) ).

thf(mforall_ind_type,type,
    mforall_ind: ( mu > $i > $o ) > $i > $o ).

%--- (new for cumulative)
thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] :
          ( ( exists_in_world @ X @ W )
         => ( Phi @ X @ W ) ) ) ) ).

%thf(mforall_ind,definition,
%    ( mforall_ind
%    = ( ^ [Phi: mu > $i > $o,W: $i] :
%        ! [X: mu] :
%          ( Phi @ X @ W ) ) )).

thf(mexists_ind_type,type,
    mexists_ind: ( mu > $i > $o ) > $i > $o ).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o] :
          ( mnot
          @ ( mforall_ind
            @ ^ [X: mu] : ( mnot @ ( Phi @ X ) ) ) ) ) ) ).

thf(mexists_prop_type,type,
    mexists_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_prop,definition,
    ( mexists_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o] :
          ( mnot
          @ ( mforall_prop
            @ ^ [P: $i > $o] : ( mnot @ ( Phi @ P ) ) ) ) ) ) ).

%----Definition of properties of accessibility relations
thf(mreflexive_type,type,
    mreflexive: ( $i > $i > $o ) > $o ).

thf(mreflexive,definition,
    ( mreflexive
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] : ( R @ S @ S ) ) ) ).

thf(msymmetric_type,type,
    msymmetric: ( $i > $i > $o ) > $o ).

thf(msymmetric,definition,
    ( msymmetric
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i] :
          ( ( R @ S @ T )
         => ( R @ T @ S ) ) ) ) ).

thf(mserial_type,type,
    mserial: ( $i > $i > $o ) > $o ).

thf(mserial,definition,
    ( mserial
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] :
        ? [T: $i] : ( R @ S @ T ) ) ) ).

thf(mtransitive_type,type,
    mtransitive: ( $i > $i > $o ) > $o ).

thf(mtransitive,definition,
    ( mtransitive
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ T @ U ) )
         => ( R @ S @ U ) ) ) ) ).

thf(meuclidean_type,type,
    meuclidean: ( $i > $i > $o ) > $o ).

thf(meuclidean,definition,
    ( meuclidean
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( R @ T @ U ) ) ) ) ).

thf(mpartially_functional_type,type,
    mpartially_functional: ( $i > $i > $o ) > $o ).

thf(mpartially_functional,definition,
    ( mpartially_functional
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( T = U ) ) ) ) ).

thf(mfunctional_type,type,
    mfunctional: ( $i > $i > $o ) > $o ).

thf(mfunctional,definition,
    ( mfunctional
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i] :
        ? [T: $i] :
          ( ( R @ S @ T )
          & ! [U: $i] :
              ( ( R @ S @ U )
             => ( T = U ) ) ) ) ) ).

thf(mweakly_dense_type,type,
    mweakly_dense: ( $i > $i > $o ) > $o ).

thf(mweakly_dense,definition,
    ( mweakly_dense
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( R @ S @ T )
         => ? [U: $i] :
              ( ( R @ S @ U )
              & ( R @ U @ T ) ) ) ) ) ).

thf(mweakly_connected_type,type,
    mweakly_connected: ( $i > $i > $o ) > $o ).

thf(mweakly_connected,definition,
    ( mweakly_connected
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ( ( R @ T @ U )
            | ( T = U )
            | ( R @ U @ T ) ) ) ) ) ).

thf(mweakly_directed_type,type,
    mweakly_directed: ( $i > $i > $o ) > $o ).

thf(mweakly_directed,definition,
    ( mweakly_directed
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i,U: $i] :
          ( ( ( R @ S @ T )
            & ( R @ S @ U ) )
         => ? [V: $i] :
              ( ( R @ T @ V )
              & ( R @ U @ V ) ) ) ) ) ).

%----Definition of validity
thf(mvalid_type,type,
    mvalid: ( $i > $o ) > $o ).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of satisfiability
thf(msatisfiable_type,type,
    msatisfiable: ( $i > $o ) > $o ).

thf(msatisfiable,definition,
    ( msatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of countersatisfiability
thf(mcountersatisfiable_type,type,
    mcountersatisfiable: ( $i > $o ) > $o ).

thf(mcountersatisfiable,definition,
    ( mcountersatisfiable
    = ( ^ [Phi: $i > $o] :
        ? [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(minvalid_type,type,
    minvalid: ( $i > $o ) > $o ).

thf(minvalid,definition,
    ( minvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL015^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL015^1 : TPTP v8.2.0. Released v5.5.0.
% Domain   : Logic Calculi (Quantified multimodal logic, cumulative domains)
% Axioms   : Cumulative domain specific axioms
% Version  : [Ben12] axioms.
% English  : 

% Refs     : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :    1 (   0 unt;   0 typ;   0 def)
%            Number of atoms       :    3 (   0 equ;   0 cnn)
%            Maximal formula atoms :    3 (   3 avg)
%            Number of connectives :    8 (   0   ~;   0   |;   1   &;   6   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   8 avg;   6 nst)
%            Number of types       :    1 (   0 usr)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   3 usr;   3 con; 0-0 aty)
%            Number of variables   :    3 (   0   ^   3   !;   0   ?;   3   :)
% SPC      : THF_SAT_EQU

% Comments : LCL015^0 and this are essentially LCL013^0.ax with the following 
%            modifications to support cumulative domains:
%            - addition of a predicate exists_in_world
%            - use of this predicate in a modified definition mforall_ind
%            - use of this predicate in an added axiom for cumulative domains
%          : Requires LCL015^0 LCL013^5
%------------------------------------------------------------------------------
thf(cumulative_ax,axiom,
    ! [X: mu,V: $i,W: $i] :
      ( ( ( exists_in_world @ X @ V )
        & ( rel_s4 @ V @ W ) )
     => ( exists_in_world @ X @ W ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL016^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL016^0 : TPTP v8.2.0. Released .0.
% Domain   : Logic Calculi (Second Order Modal Logic)
% Axioms   : Embedding of second order modal logic in simple type theory
% Version  : [Ben13] axioms.
% English  : An embedding of second order monomodal logic into simple type
%            theory. The concrete logic is base logic K.

% Refs     : [Ben13] Benzmueller (2013), Email to Geoff Sutcliffe
%          : [BP13]  Benzmueller & Paulson (2013), Quantified Multimodal Lo
% Source   : [Ben13]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   46 (  22 unt;  24 typ;  22 def)
%            Number of atoms       :   51 (  23 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   52 (   5   ~;   3   |;   4   &;  37   @)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  37 nst)
%            Number of types       :    3 (   1 usr)
%            Number of type conns  :  137 ( 137   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   26 (  23 usr;   2 con; 0-3 aty)
%            Number of variables   :   55 (  45   ^   6   !;   4   ?;  55   :)
% SPC      : TH0_SAT_EQU

% Comments : In order to obtain other logics such B or S5 one can further
%            restrict the accessibility relation. E.g. for B one can simply
%            add the axiom of symmetry for rel. For S5 one would additionally
%            postulate reflexivity and transitivity of rel.
%          : Quantifiers are provided for individuals, sets or individuals
%            (properties), and propositions. We here assume and implement
%            constant domain semantics. Respective quantifiers for varying
%            domains and cumulative domains can easily be added. An explicit
%            "existInWorlds" predicate can be introduced for this, and the
%            quantifiers would then be relativized using this predicate. The
%            generic operators mbox_generic and mdia_generic can be applied to
%            a particular accessibility relation rel to turn these generic
%            modal operators turn into a particular mbox and mdia operator for
%            rel. Hence, this axiomatization supports multimodal logics, and
%            for stating bridge rules there are different options: conditions
%            on the accessibility relations can be stated or usual bridge
%            rules can be stated unsing propositional quantification.
%------------------------------------------------------------------------------
%----Declaration of additional base type mu
thf(mu_type,type,
    mu: $tType ).

%----Equality on individuals
thf(meq_ind_type,type,
    meq_ind: mu > mu > $i > $o ).

thf(meq_ind,definition,
    ( meq_ind
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) ) ).

%----Modal operators mtrue, mfalse, mnot, mor, mand, mimplies, mequiv, ...
thf(mtrue_type,type,
    mtrue: $i > $o ).

thf(mtrue,definition,
    ( mtrue
    = ( ^ [W: $i] : $true ) ) ).

thf(mfalse_type,type,
    mfalse: $i > $o ).

thf(mfalse,definition,
    ( mfalse
    = ( ^ [W: $i] : $false ) ) ).

thf(mnot_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) ) ).

thf(mor_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) ) ).

thf(mand_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          & ( Psi @ W ) ) ) ) ).

thf(mimplies_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
         => ( Psi @ W ) ) ) ) ).

thf(mimplied_type,type,
    mimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplied,definition,
    ( mimplied
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Psi @ W )
         => ( Phi @ W ) ) ) ) ).

thf(mequiv_type,type,
    mequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mequiv,definition,
    ( mequiv
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
        <=> ( Psi @ W ) ) ) ) ).

thf(mxor_type,type,
    mxor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mxor,definition,
    ( mxor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( ( Phi @ W )
            & ~ ( Psi @ W ) )
          | ( ~ ( Phi @ W )
            & ( Psi @ W ) ) ) ) ) ).

%----Universal quantification: individuals
thf(mforall_ind_type,type,
    mforall_ind: ( mu > $i > $o ) > $i > $o ).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] : ( Phi @ X @ W ) ) ) ).

%----Universal quantification: sets of individuals (properties)
thf(mforall_indset_type,type,
    mforall_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_indset,definition,
    ( mforall_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ! [X: mu > $i > $o] : ( Phi @ X @ W ) ) ) ).

%----Universal quantification: propositions
thf(mforall_prop_type,type,
    mforall_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_prop,definition,
    ( mforall_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ! [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

%----Existential quantification: individuals
thf(mexists_ind_type,type,
    mexists_ind: ( mu > $i > $o ) > $i > $o ).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ? [X: mu] : ( Phi @ X @ W ) ) ) ).

%----Existential quantification: sets of individuals (properties)
thf(mexists_indset_type,type,
    mexists_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_indset,definition,
    ( mexists_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ? [X: mu > $i > $o] : ( Phi @ X @ W ) ) ) ).

%----Existential quantification: propositions
thf(mexists_prop_type,type,
    mexists_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_prop,definition,
    ( mexists_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ? [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

%----Generic mbox operator
thf(mbox_generic_type,type,
    mbox_generic: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mbox_generic,definition,
    ( mbox_generic
    = ( ^ [R: $i > $i > $o,Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( R @ W @ V )
          | ( Phi @ V ) ) ) ) ).

%----Generic mdia operator
thf(mdia_generic_type,type,
    mdia_generic: ( $i > $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mdia_generic,definition,
    ( mdia_generic
    = ( ^ [R: $i > $i > $o,Phi: $i > $o,W: $i] :
        ? [V: $i] :
          ( ( R @ W @ V )
          & ( Phi @ V ) ) ) ) ).

%----The accessibility relation rel
thf(rel_type,type,
    rel: $i > $i > $o ).

%----The mbox operator instantiated for rel (further mbox operators
%----for other accessibility relations can be introduced analogously)
thf(mbox_type,type,
    mbox: ( $i > $o ) > $i > $o ).

thf(mbox,definition,
    ( mbox
    = ( mbox_generic @ rel ) ) ).

%----The mdia operator instantiated for rel (further mdia operators
%----for other accessibility relations can be introduced analogously)
thf(mdia_type,type,
    mdia: ( $i > $o ) > $i > $o ).

thf(mdia,definition,
    ( mdia
    = ( mdia_generic @ rel ) ) ).

%----The notion of validity
thf(mvalid_type,type,
    mvalid: ( $i > $o ) > $o ).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(minvalid_type,type,
    minvalid: ( $i > $o ) > $o ).

thf(minvalid,definition,
    ( minvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL016^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL016^1 : TPTP v8.2.0. Released .0.
% Domain   : Logic Calculi (Second Order Modal Logic)
% Axioms   : Embedding of second order modal logic in simple type theory
% Version  : [Ben13] axioms.
% English  : Extends K to KB by adding symmetric of rel.

% Refs     : [Ben13] Benzmueller (2009), Email to Geoff Sutcliffe
%          : [BP13]  Benzmueller & Paulson (2013), Quantified Multimodal Lo
% Source   : [Ben13]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   1 unt;   1 typ;   1 def)
%            Number of atoms       :    4 (   1 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :    6 (   0   ~;   0   |;   0   &;   5   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg;   5 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :    5 (   5   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   2 usr;   1 con; 0-2 aty)
%            Number of variables   :    3 (   1   ^   2   !;   0   ?;   3   :)
% SPC      : TH0_SAT_EQU

% Comments : Requires LCL016^0.ax.
%------------------------------------------------------------------------------
%----Definition of properties of accessibility relations
thf(msymmetric_type,type,
    msymmetric: ( $i > $i > $o ) > $o ).

thf(msymmetric,definition,
    ( msymmetric
    = ( ^ [R: $i > $i > $o] :
        ! [S: $i,T: $i] :
          ( ( R @ S @ T )
         => ( R @ T @ S ) ) ) ) ).

thf(sym,axiom,
    msymmetric @ rel ).

%------------------------------------------------------------------------------

```

### ./LCL017^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL017^0 : TPTP v8.2.0. Released .0.
% Domain   : Logic Calculi (Second Order Modal Logic)
% Axioms   : Embedding of second order modal logic S5 with universal access
% Version  : [Ben16] axioms.
% English  : Embedding of second order modal logic S5 (with a universal 
%            accessibility) relation in simple type theory. In this case, the 
%            guarding accessibility constraints in the definition of box and 
%            diamond can be dropped.

% Refs     : [Ben16] Benzmueller (2016), Email to Geoff Sutcliffe
% Source   : [Ben16]
% Names    : QML_S5U.ax [Ben16]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   41 (  20 unt;  21 typ;  20 def)
%            Number of atoms       :   43 (  21 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   43 (   4   ~;   2   |;   3   &;  31   @)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  31 nst)
%            Number of types       :    3 (   1 usr)
%            Number of type conns  :  119 ( 119   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   23 (  20 usr;   2 con; 0-3 aty)
%            Number of variables   :   53 (  43   ^   6   !;   4   ?;  53   :)
% SPC      : TH0_SAT_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Declaration of additional base type mu
thf(mu_type,type,
    mu: $tType ).

%----Equality on individuals
thf(meq_ind_type,type,
    meq_ind: mu > mu > $i > $o ).

thf(meq_ind,definition,
    ( meq_ind
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) ) ).

%----Modal operators mtrue, mfalse, mnot, mor, mand, mimplies, mequiv, ...
thf(mtrue_type,type,
    mtrue: $i > $o ).

thf(mtrue,definition,
    ( mtrue
    = ( ^ [W: $i] : $true ) ) ).

thf(mfalse_type,type,
    mfalse: $i > $o ).

thf(mfalse,definition,
    ( mfalse
    = ( ^ [W: $i] : $false ) ) ).

thf(mnot_type,type,
    mnot: ( $i > $o ) > $i > $o ).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) ) ).

thf(mor_type,type,
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) ) ).

thf(mand_type,type,
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          & ( Psi @ W ) ) ) ) ).

thf(mimplies_type,type,
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
         => ( Psi @ W ) ) ) ) ).

thf(mimplied_type,type,
    mimplied: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mimplied,definition,
    ( mimplied
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Psi @ W )
         => ( Phi @ W ) ) ) ) ).

thf(mequiv_type,type,
    mequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mequiv,definition,
    ( mequiv
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
        <=> ( Psi @ W ) ) ) ) ).

thf(mxor_type,type,
    mxor: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(mxor,definition,
    ( mxor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( ( Phi @ W )
            & ~ ( Psi @ W ) )
          | ( ~ ( Phi @ W )
            & ( Psi @ W ) ) ) ) ) ).

%----Universal quantification: individuals
thf(mforall_ind_type,type,
    mforall_ind: ( mu > $i > $o ) > $i > $o ).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] : ( Phi @ X @ W ) ) ) ).

%----Universal quantification: sets of individuals (properties)
thf(mforall_indset_type,type,
    mforall_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_indset,definition,
    ( mforall_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ! [X: mu > $i > $o] : ( Phi @ X @ W ) ) ) ).

%----Universal quantification: propositions
thf(mforall_prop_type,type,
    mforall_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mforall_prop,definition,
    ( mforall_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ! [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

%----Existential quantification: individuals
thf(mexists_ind_type,type,
    mexists_ind: ( mu > $i > $o ) > $i > $o ).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ? [X: mu] : ( Phi @ X @ W ) ) ) ).

%----Existential quantification: sets of individuals (properties)
thf(mexists_indset_type,type,
    mexists_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_indset,definition,
    ( mexists_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ? [X: mu > $i > $o] : ( Phi @ X @ W ) ) ) ).

%----Existential quantification: propositions
thf(mexists_prop_type,type,
    mexists_prop: ( ( $i > $o ) > $i > $o ) > $i > $o ).

thf(mexists_prop,definition,
    ( mexists_prop
    = ( ^ [Phi: ( $i > $o ) > $i > $o,W: $i] :
        ? [P: $i > $o] : ( Phi @ P @ W ) ) ) ).

%----Box operator (exploting universal accessibility)
thf(mbox_type,type,
    mbox: ( $i > $o ) > $i > $o ).

thf(mbox,definition,
    ( mbox
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] : ( Phi @ V ) ) ) ).

%----Diamond operator
thf(mdia_type,type,
    mdia: ( $i > $o ) > $i > $o ).

thf(mdia,definition,
    ( mdia
    = ( ^ [Phi: $i > $o,W: $i] :
        ? [V: $i] : ( Phi @ V ) ) ) ).

%----The notion of validity
thf(mvalid_type,type,
    mvalid: ( $i > $o ) > $o ).

thf(mvalid,definition,
    ( mvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] : ( Phi @ W ) ) ) ).

%----Definition of invalidity
thf(minvalid_type,type,
    minvalid: ( $i > $o ) > $o ).

thf(minvalid,definition,
    ( minvalid
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ~ ( Phi @ W ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LCL017^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : LCL017^1 : TPTP v8.2.0. Released v7.5.0.
% Domain   : Logic Calculi (Modal Logic)
% Axioms   : Variable Domain Quantifiers for Modal Logic
% Version  : [Gus20] axioms.
% English  : 

% Refs     : [Gus20] Gustafsson (2020), Email to Geoff Sutcliffe
% Source   : [Gus20]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   3 unt;   3 typ;   2 def)
%            Number of atoms       :    9 (   2 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   11 (   0   ~;   0   |;   0   &;  10   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    5 (   2 avg;  10 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   14 (  14   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    6 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    7 (   4   ^   2   !;   1   ?;   7   :)
% SPC      : TH0_SAT_EQU_NAR

% Comments : Combine with LCL016^0 for Quantified Modal Logic K wth variable 
%            domain.
%          : Combine with LCL016^0 and LCL016^1 for Quantified Modal Logic KB 
%            with variable domain.
%          : Combine with LCL017^0 for Quantified Modal Logic S5 with variable 
%            domain.
%------------------------------------------------------------------------------
thf(eiw_ind,type,
    eiw_ind: $i > mu > $o ).

thf(nonempty_ind,axiom,
    ! [V: $i] :
    ? [X: mu] : ( eiw_ind @ V @ X ) ).

thf(mforall_eiw_ind_type,type,
    mforall_eiw_ind: ( mu > $i > $o ) > $i > $o ).

thf(mforall_eiw_ind,definition,
    ( mforall_eiw_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] :
          ( ( eiw_ind @ W @ X )
         => ( Phi @ X @ W ) ) ) ) ).

thf(mexists_eiw_ind_type,type,
    mexists_eiw_ind: ( mu > $i > $o ) > $i > $o ).

thf(mexists_eiw_ind,definition,
    ( mexists_eiw_ind
    = ( ^ [Phi: mu > $i > $o] :
          ( mnot
          @ ( mforall_eiw_ind
            @ ^ [X: mu] : ( mnot @ ( Phi @ X ) ) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./LDA001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : LDA001-0 : TPTP v8.2.0. Bugfixed v2.6.0.
% Domain   : LD-Algebras (Embedding algebras)
% Axioms   : Embedding algebra
% Version  : [Jec93] axioms : Incomplete.
% English  : LD-algebras are related to large cardinals. Under a very
%            strong large cardinal assumption, the free-monogenic
%            LD-algebra can be represented by an algebra of elementary
%            embeddings. Theorems about this algebra can be proved from
%            a small number of properties, suggesting the definition
%            of an embedding algebra.

% Refs     : [Jec93] Jech (1993), LD-Algebras
%          : [Jec02] Jech (2002), Email to Geoff Sutcliffe
% Source   : [Jec93]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    9 (   4 unt;   2 nHn;   3 RR)
%            Number of literals    :   16 (   5 equ;   5 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   21 (   0 sgn)
% SPC      : 

% Comments : [Jec93] says, "Even though axioms for embedding algebras
%            include additional properties to those listed below, many
%            results can be proved from these axioms."
% Bugfixes : v2.6.0 - Fixed axioms; they were unsatisfiable [Jec02]
%--------------------------------------------------------------------------
%----A1  x(yz)=(xy)(xz)
cnf(a1,axiom,
    f(X,f(Y,Z)) = f(f(X,Y),f(X,Z)) ).

%----A1a a(x,a(y,z)) = a(x*y,a(x,z))
cnf(a1a,axiom,
    a(X,a(Y,Z)) = a(f(X,Y),a(X,Z)) ).

%----A2  cr(u*v) = a(u,cr(v))
cnf(a2,axiom,
    critical_point(f(U,V)) = a(U,critical_point(V)) ).

%----B1  -(x<x)
cnf(b1,axiom,
    ~ less(X,X) ).

%----B2  linear
cnf(b2,axiom,
    ( less(X,Y)
    | less(Y,X)
    | X = Y ) ).

%----B3  transitive
cnf(b3,axiom,
    ( ~ less(X,Y)
    | ~ less(Y,Z)
    | less(X,Z) ) ).

%----B4  if x<y then ux<uy
cnf(b4,axiom,
    ( ~ less(X,Y)
    | less(a(U,X),a(U,Y)) ) ).

%----C2  if x<crit(u) then ux=x
cnf(c2,axiom,
    ( ~ less(X,critical_point(U))
    | a(U,X) = X ) ).

%----C3  x<crit(u) or x<ux
cnf(c3,axiom,
    ( less(X,critical_point(U))
    | less(X,a(U,X)) ) ).

%--------------------------------------------------------------------------

```

### ./MAT001^0.ax

Very long 20534

### ./MED001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : MED001+0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Medicine
% Axioms   : Physiology Diabetes Mellitus type 2
% Version  : [HLB05] axioms : Especial.
% English  : Physiological mechanisms of diabetes mellitus type 2

% Refs     : [HLB05] Hommersom et al. (2005), Automated Theorem Proving for
%          : [Hom06] Hommersom (2006), Email to G. Sutcliffe
% Source   : [Hom06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   18 (   1 unt;   0 def)
%            Number of atoms       :   76 (   0 equ)
%            Maximal formula atoms :   11 (   4 avg)
%            Number of connectives :   95 (  37   ~;  12   |;  15   &)
%                                         (   0 <=>;  31  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   6 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   15 (  15 usr;   0 prp; 1-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   42 (  42   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(irreflexivity_gt,axiom,
    ! [X] : ~ gt(X,X) ).

fof(transitivity_gt,axiom,
    ! [X,Y,Z] :
      ( ( gt(X,Y)
        & gt(Y,Z) )
     => gt(X,Z) ) ).

fof(xorcapacity1,axiom,
    ! [X0] :
      ( bcapacityne(X0)
      | bcapacityex(X0)
      | bcapacitysn(X0) ) ).

fof(xorcapacity2,axiom,
    ! [X0] :
      ( ~ bcapacityne(X0)
      | ~ bcapacityex(X0) ) ).

fof(xorcapacity3,axiom,
    ! [X0] :
      ( ~ bcapacityne(X0)
      | ~ bcapacitysn(X0) ) ).

fof(xorcapacity4,axiom,
    ! [X0] :
      ( ~ bcapacityex(X0)
      | ~ bcapacitysn(X0) ) ).

fof(xorcondition1,axiom,
    ! [X0] :
      ( conditionhyper(X0)
      | conditionhypo(X0)
      | conditionnormo(X0) ) ).

fof(xorcondition2,axiom,
    ! [X0] :
      ( ~ conditionhyper(X0)
      | ~ conditionhypo(X0) ) ).

fof(xorcondition3,axiom,
    ! [X0] :
      ( ~ conditionhyper(X0)
      | ~ conditionnormo(X0) ) ).

fof(xorcondition4,axiom,
    ! [X0] :
      ( ~ conditionhypo(X0)
      | ~ conditionnormo(X0) ) ).

fof(insulin_effect,axiom,
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => drugi(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ( uptakelg(X1)
            & uptakepg(X1) ) ) ) ).

fof(liver_glucose,axiom,
    ! [X0,X1] :
      ( ~ gt(X0,X1)
     => ( uptakelg(X1)
       => ~ releaselg(X1) ) ) ).

fof(sulfonylurea_effect,axiom,
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => drugsu(X1) )
        & ~ bcapacityex(X0) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => bsecretioni(X1) ) ) ).

fof(biguanide_effect,axiom,
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => drugbg(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ~ releaselg(X1) ) ) ).

fof(sn_cure_1,axiom,
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => bsecretioni(X1) )
        & bcapacitysn(X0)
        & qilt27(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) ).

fof(sn_cure_2,axiom,
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => ~ releaselg(X1) )
        & bcapacitysn(X0)
        & ~ qilt27(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) ).

fof(ne_cure,axiom,
    ! [X0] :
      ( ( ( ! [X1] :
              ( ~ gt(X0,X1)
             => ~ releaselg(X1) )
          | ! [X1] :
              ( ~ gt(X0,X1)
             => uptakepg(X1) ) )
        & bcapacityne(X0)
        & ! [X1] :
            ( ~ gt(X0,X1)
           => bsecretioni(X1) )
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) ).

fof(ex_cure,axiom,
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => uptakelg(X1) )
        & ! [X1] :
            ( ~ gt(X0,X1)
           => uptakepg(X1) )
        & bcapacityex(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ( conditionnormo(X1)
            | conditionhypo(X1) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./MED001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : MED001+1 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Medicine
% Axioms   : "Completed" Physiology Diabetes Mellitus type 2
% Version  : [HLB05] axioms : Especial.
% English  : Completed theory of diabetes mellitus type 2 mechanisms

% Refs     : [HLB05] Hommersom et al. (2005), Automated Theorem Proving for
%          : [Hom06] Hommersom (2006), Email to G. Sutcliffe
% Source   : [Hom06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   22 (   0 unt;   0 def)
%            Number of atoms       :  114 (   0 equ)
%            Maximal formula atoms :   30 (   5 avg)
%            Number of connectives :  137 (  45   ~;  21   |;  30   &)
%                                         (   0 <=>;  41  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (   6 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   0 prp; 1-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   51 (  48   !;   3   ?)
% SPC      : 

% Comments : Requires MED001+0.ax
%------------------------------------------------------------------------------
fof(xorstep1,axiom,
    ! [X0] :
      ( s0(X0)
      | s1(X0)
      | s2(X0)
      | s3(X0) ) ).

fof(xorstep2,axiom,
    ! [X0] :
      ( ~ s0(X0)
      | ~ s1(X0) ) ).

fof(xorstep3,axiom,
    ! [X0] :
      ( ~ s0(X0)
      | ~ s2(X0) ) ).

fof(xorstep4,axiom,
    ! [X0] :
      ( ~ s0(X0)
      | ~ s3(X0) ) ).

fof(xorstep5,axiom,
    ! [X0] :
      ( ~ s1(X0)
      | ~ s2(X0) ) ).

fof(xorstep6,axiom,
    ! [X0] :
      ( ~ s1(X0)
      | ~ s3(X0) ) ).

fof(xorstep7,axiom,
    ! [X0] :
      ( ~ s2(X0)
      | ~ s3(X0) ) ).

fof(normo,axiom,
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) )
     => ( ( ! [X1] :
              ( ~ gt(X0,X1)
             => bsecretioni(X1) )
          & bcapacitysn(X0)
          & qilt27(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ! [X1] :
              ( ~ gt(X0,X1)
             => ~ releaselg(X1) )
          & bcapacitysn(X0)
          & ~ qilt27(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ( ! [X1] :
                ( ~ gt(X0,X1)
               => ~ releaselg(X1) )
            | ! [X1] :
                ( ~ gt(X0,X1)
               => uptakepg(X1) ) )
          & bcapacityne(X0)
          & ! [X1] :
              ( ~ gt(X0,X1)
             => bsecretioni(X1) )
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ! [X1] :
              ( ~ gt(X0,X1)
             => uptakelg(X1) )
          & ! [X1] :
              ( ~ gt(X0,X1)
             => uptakepg(X1) )
          & bcapacityex(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) ) ) ) ).

fof(step1,axiom,
    ! [X0] :
      ( ( s1(X0)
        & qilt27(X0) )
     => drugsu(X0) ) ).

fof(step2,axiom,
    ! [X0] :
      ( ( s1(X0)
        & ~ qilt27(X0) )
     => drugbg(X0) ) ).

fof(step3,axiom,
    ! [X0] :
      ( s2(X0)
     => ( drugbg(X0)
        & drugsu(X0) ) ) ).

fof(step4,axiom,
    ! [X0] :
      ( s3(X0)
     => ( ( drugi(X0)
          & ( drugsu(X0)
            | drugbg(X0) ) )
        | drugi(X0) ) ) ).

fof(bgcomp,axiom,
    ! [X0] :
      ( drugbg(X0)
     => ( ( s1(X0)
          & ~ qilt27(X0) )
        | s2(X0)
        | s3(X0) ) ) ).

fof(sucomp,axiom,
    ! [X0] :
      ( drugsu(X0)
     => ( ( s1(X0)
          & qillt27(X0) )
        | s2(X0)
        | s3(X0) ) ) ).

fof(insulincomp,axiom,
    ! [X0] :
      ( drugi(X0)
     => s3(X0) ) ).

fof(insulin_completion,axiom,
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => uptakelg(X1) )
        | ! [X1] :
            ( ~ gt(X0,X1)
           => uptakepg(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => drugi(X1) ) ) ).

fof(uptake_completion,axiom,
    ! [X0,X1] :
      ( ~ gt(X0,X1)
     => ( ~ releaselg(X1)
       => uptakelg(X1) ) ) ).

fof(su_completion,axiom,
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => bsecretioni(X1) )
     => ( ! [X1] :
            ( ~ gt(X0,X1)
           => drugsu(X1) )
        & ~ bcapacityex(X0) ) ) ).

fof(bg_completion,axiom,
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => ~ releaselg(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => drugbg(X1) ) ) ).

fof(trans_ax1,axiom,
    ! [X0] :
      ( ( s0(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s1(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) ) ) ) ).

fof(trans_ax2,axiom,
    ! [X0] :
      ( ( s1(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s2(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) )
          & ( bcapacityne(X1)
            | bcapacityex(X1) ) ) ) ).

fof(trans_ax3,axiom,
    ! [X0] :
      ( ( s2(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s3(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) )
          & bcapacityex(X1) ) ) ).

%------------------------------------------------------------------------------

```

### ./MED002+0.ax

Very long 1705620

### ./MGT001+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : MGT001+0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Axioms   : Inequalities.
% Version  : [Han98] axioms.
% English  :

% Refs     : [Kam00] Kamps (2000), Email to G. Sutcliffe
%            [CH00]  Carroll & Hannan (2000), The Demography of Corporation
%            [Han98] Hannan (1998), Rethinking Age Dependence in Organizati
% Source   : [Kam00]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   0 unt;   0 def)
%            Number of atoms       :   16 (   3 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :   11 (   1   ~;   4   |;   2   &)
%                                         (   3 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   5 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   13 (  13   !;   0   ?)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----Definition of smaller_or_equal (i.t.o. smaller and equal).
fof(definition_smaller_or_equal,axiom,
    ! [X,Y] :
      ( smaller_or_equal(X,Y)
    <=> ( smaller(X,Y)
        | X = Y ) ) ).

%%----Definition of smaller_or_equal (i.t.o. greater).
%input_formula(definition_smaller_or_equal, axiom, (
%    ! [X,Y] :
%      ( smaller_or_equal(X,Y)
%    <=> ( ~ greater(X,Y) ) ) )).

%----Definition of greater_or_equal (i.t.o. greater and equal).
fof(definition_greater_or_equal,axiom,
    ! [X,Y] :
      ( greater_or_equal(X,Y)
    <=> ( greater(X,Y)
        | X = Y ) ) ).

%%----Definition of greater_or_equal (i.t.o. greater and equal).
%input_formula(definition_greater_or_equal, axiom, (
%    ! [X,Y] :
%      ( greater_or_equal(X,Y)
%    <=> ( ~ greater(Y,X) ) ) )).

%----Definition of smaller (i.t.o. greater).
fof(definition_smaller,axiom,
    ! [X,Y] :
      ( smaller(X,Y)
    <=> greater(Y,X) ) ).

%----Our notion of greater is strict (irreflexive and antisymmetric).
fof(meaning_postulate_greater_strict,axiom,
    ! [X,Y] :
      ~ ( greater(X,Y)
        & greater(Y,X) ) ).

%%----Derivable from above.
%input_formula(meaning_postulate_greater_strict2, axiom, (
%    ! [X] :
%      ( ~ greater(X,X) ) )).

%----Our notion of greater is transitive.
fof(meaning_postulate_greater_transitive,axiom,
    ! [X,Y,Z] :
      ( ( greater(X,Y)
        & greater(Y,Z) )
     => greater(X,Z) ) ).

%----Hazards of mortality are comparable.
%input_formula(background_ass_a1, axiom, (
%  ! [X,T0,T] :
%    ( organization(X)
%   => ( ( greater(hazard_of_mortality(X,T),hazard_of_mortality(X,T0))
%        | equal(hazard_of_mortality(X,T),hazard_of_mortality(X,T0)) )
%       => smaller(hazard_of_mortality(X,T),hazard_of_mortality(X,T0)) ) ) )).

%----Trichotomy statement for everything.
%input_formula(meaning_postulate_greater_comparable, axiom, (
%    ! [X,Y] :
%      ( greater(Y,X)
%      | equal(X,Y)
%      | greater(X,Y) ) )).
fof(meaning_postulate_greater_comparable,axiom,
    ! [X,Y] :
      ( smaller(X,Y)
      | X = Y
      | greater(X,Y) ) ).

%--------------------------------------------------------------------------

```

### ./MGT001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : MGT001-0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Axioms   : Inequalities.
% Version  : [Han98] axioms.
% English  :

% Refs     : [Kam00] Kamps (2000), Email to G. Sutcliffe
%            [CH00]  Carroll & Hannan (2000), The Demography of Corporation
%            [Han98] Hannan (1998), Rethinking Age Dependence in Organizati
% Source   : [Kam00]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   0 unt;   3 nHn;  10 RR)
%            Number of literals    :   26 (   5 equ;  12 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   23 (   0 sgn)
% SPC      : 

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT001+0.ax
%--------------------------------------------------------------------------
cnf(definition_smaller_or_equal_1,axiom,
    ( ~ smaller_or_equal(A,B)
    | smaller(A,B)
    | A = B ) ).

cnf(definition_smaller_or_equal_2,axiom,
    ( ~ smaller(A,B)
    | smaller_or_equal(A,B) ) ).

cnf(definition_smaller_or_equal_3,axiom,
    ( A != B
    | smaller_or_equal(A,B) ) ).

cnf(definition_greater_or_equal_4,axiom,
    ( ~ greater_or_equal(A,B)
    | greater(A,B)
    | A = B ) ).

cnf(definition_greater_or_equal_5,axiom,
    ( ~ greater(A,B)
    | greater_or_equal(A,B) ) ).

cnf(definition_greater_or_equal_6,axiom,
    ( A != B
    | greater_or_equal(A,B) ) ).

cnf(definition_smaller_7,axiom,
    ( ~ smaller(A,B)
    | greater(B,A) ) ).

cnf(definition_smaller_8,axiom,
    ( ~ greater(A,B)
    | smaller(B,A) ) ).

cnf(meaning_postulate_greater_strict_9,axiom,
    ( ~ greater(A,B)
    | ~ greater(B,A) ) ).

cnf(meaning_postulate_greater_transitive_10,axiom,
    ( ~ greater(A,B)
    | ~ greater(B,C)
    | greater(A,C) ) ).

cnf(meaning_postulate_greater_comparable_11,axiom,
    ( smaller(A,B)
    | A = B
    | greater(A,B) ) ).

%--------------------------------------------------------------------------

```

### ./MSC001-0.ax

Very long 4534

### ./MSC001-1.ax

Very long 6962

### ./MSC001-2.ax

Very long 794

### ./MVA001-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : MVA001-0 : TPTP v8.2.0. Released v8.0.0.
% Domain   : MV-algebras
% Axioms   : Generalized MV algebras (equality)
% Version  : [Ver10] (equality) axioms.
% English  :

% Refs     : [GT05]  Galatos & Tsinakis (2005), Generalized MV-algebras
%          : [GJ+07] Galatos et al. (2007), Residuated Lattices: An Algebra
%          : [Ver10] Veroff (2010), Email to Geoff Sutcliffe
%          : [Sma21] Smallbone (2021), Email to Geoff Sutcliffe
% Source   : [Ver10]
% Names    : gmv+1.ax [Sma21]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   18 (  18 unt;   0 nHn;   0 RR)
%            Number of literals    :   18 (  18 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   7 usr;   1 con; 0-2 aty)
%            Number of variables   :   39 (   6 sgn)
% SPC      : CNF_SAT_RFO_PEQ_UEQ

% Comments :
%------------------------------------------------------------------------------
cnf(associativity_of_meet,axiom,
    ( meet(meet(X,Y),Z) = meet(X,meet(Y,Z)) )).

cnf(associativity_of_join,axiom,
    ( join(join(X,Y),Z) = join(X,join(Y,Z)) )).

cnf(idempotence_of_meet,axiom,
    ( meet(X,X) = X )).

cnf(idempotence_of_join,axiom,
    ( join(X,X) = X )).

cnf(commutativity_of_meet,axiom,
    ( meet(X,Y) = meet(Y,X) )).

cnf(commutativity_of_join,axiom,
    ( join(X,Y) = join(Y,X) )).

cnf(absorption_a,axiom,
    ( join(meet(X,Y),X) = X )).

cnf(absorption_b,axiom,
    ( meet(join(X,Y),X) = X )).

cnf(residual_a,axiom,
    ( join(op(X,meet(ld(X,Z),Y)),Z) = Z )).

cnf(residual_b,axiom,
    ( join(op(meet(Y,rd(Z,X)),X),Z) = Z )).

cnf(residual_c,axiom,
    ( meet(ld(X,join(op(X,Y),Z)),Y) = Y )).

cnf(residual_d,axiom,
    ( meet(rd(join(op(Y,X),Z),X),Y) = Y )).

cnf(monoid_associativity,axiom,
    ( op(op(X,Y),Z) = op(X,op(Y,Z)) )).

cnf(left_monoid_unit,axiom,
    ( op(unit,X) = X )).

cnf(right_monoid_unit,axiom,
    ( op(X,unit) = X )).

cnf(generalized_mv_algebra_a,axiom,
    ( join(X,Y) = rd(X,ld(join(X,Y),X)) )).

cnf(generalized_mv_algebra_b,axiom,
    ( join(X,Y) = ld(rd(X,join(X,Y)),X) )).

cnf(definition_of_at,axiom,
    ( at(X,Y) = op(op(X,ld(X,unit)),ld(ld(Y,unit),unit)) )).

%------------------------------------------------------------------------------

```

### ./NLP001+0.ax

Very long 3080612

## Number Theory

### ./NUM001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM001-0 : TPTP v8.2.0. Bugfixed v4.0.0.
% Domain   : Number Theory
% Axioms   : Number theory axioms
% Version  : [LS74] axioms : Incomplete.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   10 (   1 sgn)
% SPC      : 

% Comments :
% Bugfixes : v4.0.0 - Duplicate successor_equality1 removed.
%--------------------------------------------------------------------------
cnf(adding_zero,axiom,
    equalish(add(A,n0),A) ).

cnf(addition,axiom,
    equalish(add(A,successor(B)),successor(add(A,B))) ).

cnf(times_zero,axiom,
    equalish(multiply(A,n0),n0) ).

cnf(times,axiom,
    equalish(multiply(A,successor(B)),add(multiply(A,B),A)) ).

cnf(successor_equality1,axiom,
    ( ~ equalish(successor(A),successor(B))
    | equalish(A,B) ) ).

cnf(successor_substitution,axiom,
    ( ~ equalish(A,B)
    | equalish(successor(A),successor(B)) ) ).

%--------------------------------------------------------------------------

```

### ./NUM001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Number Theory
% Axioms   : Number theory less axioms
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   0 unt;   0 nHn;   3 RR)
%            Number of literals    :    7 (   0 equ;   4 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :    8 (   1 sgn)
% SPC      : 

% Comments : Requires NUM001-0.ax
%--------------------------------------------------------------------------
cnf(transitivity_of_less,axiom,
    ( ~ less(A,B)
    | ~ less(C,A)
    | less(C,B) ) ).

cnf(smaller_number,axiom,
    ( ~ equalish(add(successor(A),B),C)
    | less(B,C) ) ).

cnf(less_lemma,axiom,
    ( ~ less(A,B)
    | equalish(add(successor(predecessor_of_1st_minus_2nd(B,A)),A),B) ) ).

%--------------------------------------------------------------------------

```

### ./NUM001-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM001-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Number Theory
% Axioms   : Number theory div axioms
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   0 unt;   1 nHn;   3 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    6 (   0 sgn)
% SPC      : 

% Comments : Requires NUM001-0.ax NUM001-1.ax
%--------------------------------------------------------------------------
cnf(divides_only_less_or_equal,axiom,
    ( ~ divides(A,B)
    | less(A,B)
    | equalish(A,B) ) ).

cnf(divides_if_less,axiom,
    ( ~ less(A,B)
    | divides(A,B) ) ).

cnf(divides_if_equal,axiom,
    ( ~ equalish(A,B)
    | divides(A,B) ) ).

%--------------------------------------------------------------------------

```

### ./NUM002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Number theory
% Axioms   : Number theory (equality) axioms
% Version  : [LS74] (equality) axioms : Biased.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   12 (   7 unt;   0 nHn;   5 RR)
%            Number of literals    :   22 (   0 equ;  10 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 2-2 aty)
%            Number of variables   :   35 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(reflexivity,axiom,
    equalish(A,A) ).

cnf(transitivity,axiom,
    ( ~ equalish(A,B)
    | ~ equalish(B,C)
    | equalish(A,C) ) ).

cnf(commutativity_of_addition,axiom,
    equalish(add(A,B),add(B,A)) ).

cnf(associativity_of_addition,axiom,
    equalish(add(A,add(B,C)),add(add(A,B),C)) ).

cnf(addition_inverts_subtraction1,axiom,
    equalish(subtract(add(A,B),B),A) ).

cnf(addition_inverts_subtraction2,axiom,
    equalish(A,subtract(add(A,B),B)) ).

cnf(commutativity1,axiom,
    equalish(add(subtract(A,B),C),subtract(add(A,C),B)) ).

cnf(commutativity2,axiom,
    equalish(subtract(add(A,B),C),add(subtract(A,C),B)) ).

cnf(add_substitution1,axiom,
    ( ~ equalish(A,B)
    | ~ equalish(C,add(A,D))
    | equalish(C,add(B,D)) ) ).

cnf(add_substitution2,axiom,
    ( ~ equalish(A,B)
    | ~ equalish(C,add(D,A))
    | equalish(C,add(D,B)) ) ).

cnf(subtract_substitution1,axiom,
    ( ~ equalish(A,B)
    | ~ equalish(C,subtract(A,D))
    | equalish(C,subtract(B,D)) ) ).

cnf(subtract_substitution2,axiom,
    ( ~ equalish(A,B)
    | ~ equalish(C,subtract(D,A))
    | equalish(C,subtract(D,B)) ) ).

%--------------------------------------------------------------------------

```

### ./NUM003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM003-0 : TPTP v8.2.0. Bugfixed v1.2.1.
% Domain   : Number Theory
% Axioms   : Number theory axioms, based on Godel set theory
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   54 (   0 unt;  32 nHn;  54 RR)
%            Number of literals    :  215 (  16 equ; 116 neg)
%            Maximal clause size   :    7 (   3 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :   29 (  29 usr;   7 con; 0-3 aty)
%            Number of variables   :   90 (   0 sgn)
% SPC      : 

% Comments : Requires SET003-0.ax ALG001-0.ax
% Bugfixes : v1.2.1 - Clauses finite3 and finite5 fixed.
%--------------------------------------------------------------------------
%----Definition of natural_numbers (natural numbers)
cnf(natural_numbers1,axiom,
    ( ~ member(Z,natural_numbers)
    | ~ little_set(Xs)
    | ~ member(empty_set,Xs)
    | member(f43(Z,Xs),Xs)
    | member(Z,Xs) ) ).

cnf(natural_numbers2,axiom,
    ( ~ member(Z,natural_numbers)
    | ~ little_set(Xs)
    | ~ member(empty_set,Xs)
    | ~ member(successor(f43(Z,Xs)),Xs)
    | member(Z,Xs) ) ).

cnf(natural_numbers3,axiom,
    ( member(Z,natural_numbers)
    | ~ little_set(Z)
    | little_set(f44(Z)) ) ).

cnf(natural_numbers4,axiom,
    ( member(Z,natural_numbers)
    | ~ little_set(Z)
    | member(empty_set,f44(Z)) ) ).

cnf(natural_numbers5,axiom,
    ( member(Z,natural_numbers)
    | ~ little_set(Z)
    | ~ member(Xk,f44(Z))
    | member(successor(Xk),f44(Z)) ) ).

cnf(natural_numbers6,axiom,
    ( member(Z,natural_numbers)
    | ~ member(Z,f44(Z)) ) ).

%----Definition of plus
cnf(plus1,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | member(f45(Z,Xs),natural_numbers)
    | member(f46(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus2,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | member(f45(Z,Xs),natural_numbers)
    | member(f47(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus3,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | member(f45(Z,Xs),natural_numbers)
    | member(f48(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus4,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | member(f45(Z,Xs),natural_numbers)
    | member(ordered_pair(ordered_pair(f46(Z,Xs),f47(Z,Xs)),f48(Z,Xs)),Xs)
    | member(Z,Xs) ) ).

cnf(plus5,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | member(f45(Z,Xs),natural_numbers)
    | ~ member(ordered_pair(ordered_pair(successor(f46(Z,Xs)),f47(Z,Xs)),successor(f48(Z,Xs))),Xs)
    | member(Z,Xs) ) ).

cnf(plus6,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f45(Z,Xs)),f45(Z,Xs)),Xs)
    | member(f46(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus7,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f45(Z,Xs)),f45(Z,Xs)),Xs)
    | member(f47(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus8,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f45(Z,Xs)),f45(Z,Xs)),Xs)
    | member(f48(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(plus9,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f45(Z,Xs)),f45(Z,Xs)),Xs)
    | member(ordered_pair(ordered_pair(f46(Z,Xs),f47(Z,Xs)),f48(Z,Xs)),Xs)
    | member(Z,Xs) ) ).

cnf(plus10,axiom,
    ( ~ member(Z,plus)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f45(Z,Xs)),f45(Z,Xs)),Xs)
    | ~ member(ordered_pair(ordered_pair(successor(f46(Z,Xs)),f47(Z,Xs)),successor(f48(Z,Xs))),Xs)
    | member(Z,Xs) ) ).

cnf(plus11,axiom,
    ( member(Z,plus)
    | ~ little_set(Z)
    | little_set(f49(Z)) ) ).

cnf(plus12,axiom,
    ( member(Z,plus)
    | ~ little_set(Z)
    | ~ member(Xi,natural_numbers)
    | member(ordered_pair(ordered_pair(empty_set,Xi),Xi),f49(Z)) ) ).

cnf(plus13,axiom,
    ( member(Z,plus)
    | ~ little_set(Z)
    | ~ member(Uu1,natural_numbers)
    | ~ member(Xj,natural_numbers)
    | ~ member(Xk,natural_numbers)
    | ~ member(ordered_pair(ordered_pair(Uu1,Xj),Xk),f49(Z))
    | member(ordered_pair(ordered_pair(successor(Uu1),Xj),successor(Xk)),f49(Z)) ) ).

cnf(plus14,axiom,
    ( member(Z,plus)
    | ~ member(Z,f49(Z)) ) ).

%----Definition of times
cnf(times1,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | member(f50(Z,Xs),natural_numbers)
    | member(f51(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times2,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | member(f50(Z,Xs),natural_numbers)
    | member(f52(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times3,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | member(f50(Z,Xs),natural_numbers)
    | member(f53(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times4,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | member(f50(Z,Xs),natural_numbers)
    | member(ordered_pair(ordered_pair(f51(Z,Xs),f52(Z,Xs)),f53(Z,Xs)),Xs)
    | member(Z,Xs) ) ).

cnf(times5,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | member(f50(Z,Xs),natural_numbers)
    | ~ member(ordered_pair(ordered_pair(successor(f51(Z,Xs)),f52(Z,Xs)),apply_to_two_arguments(plus,f53(Z,Xs),f52(Z,Xs))),Xs)
    | member(Z,Xs) ) ).

cnf(times6,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f50(Z,Xs)),empty_set),Xs)
    | member(f51(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times7,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f50(Z,Xs)),empty_set),Xs)
    | member(f52(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times8,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f50(Z,Xs)),empty_set),Xs)
    | member(f53(Z,Xs),natural_numbers)
    | member(Z,Xs) ) ).

cnf(times9,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f50(Z,Xs)),empty_set),Xs)
    | member(ordered_pair(ordered_pair(f51(Z,Xs),f52(Z,Xs)),f53(Z,Xs)),Xs)
    | member(Z,Xs) ) ).

cnf(times10,axiom,
    ( ~ member(Z,times)
    | ~ little_set(Xs)
    | ~ member(ordered_pair(ordered_pair(empty_set,f50(Z,Xs)),empty_set),Xs)
    | ~ member(ordered_pair(ordered_pair(successor(f51(Z,Xs)),f52(Z,Xs)),apply_to_two_arguments(plus,f53(Z,Xs),f52(Z,Xs))),Xs)
    | member(Z,Xs) ) ).

cnf(times11,axiom,
    ( member(Z,times)
    | ~ little_set(Z)
    | little_set(f54(Z)) ) ).

cnf(times12,axiom,
    ( member(Z,times)
    | ~ little_set(Z)
    | ~ member(Xi,natural_numbers)
    | member(ordered_pair(ordered_pair(empty_set,Xi),empty_set),f54(Z)) ) ).

cnf(times13,axiom,
    ( member(Z,times)
    | ~ little_set(Z)
    | ~ member(Uu2,natural_numbers)
    | ~ member(Xj,natural_numbers)
    | ~ member(Xk,natural_numbers)
    | ~ member(ordered_pair(ordered_pair(Uu2,Xj),Xk),f54(Z))
    | member(ordered_pair(ordered_pair(successor(Uu2),Xj),apply_to_two_arguments(plus,Xk,Xj)),f54(Z)) ) ).

cnf(times14,axiom,
    ( member(Z,times)
    | ~ member(Z,f54(Z)) ) ).

%----Definition of prime_numbers
cnf(prime_numbers1,axiom,
    ( ~ member(Z,prime_numbers)
    | member(Z,natural_numbers) ) ).

cnf(prime_numbers2,axiom,
    ( ~ member(Z,prime_numbers)
    | Z != empty_set ) ).

cnf(prime_numbers3,axiom,
    ( ~ member(Z,prime_numbers)
    | Z != successor(empty_set) ) ).

cnf(prime_numbers4,axiom,
    ( ~ member(Z,prime_numbers)
    | ~ member(U,natural_numbers)
    | ~ member(V,natural_numbers)
    | apply_to_two_arguments(times,U,V) != Z
    | member(U,non_ordered_pair(successor(empty_set),Z)) ) ).

cnf(prime_numbers5,axiom,
    ( member(Z,prime_numbers)
    | ~ member(Z,natural_numbers)
    | Z = empty_set
    | Z = successor(empty_set)
    | member(f55(Z),natural_numbers) ) ).

cnf(prime_numbers6,axiom,
    ( member(Z,prime_numbers)
    | ~ member(Z,natural_numbers)
    | Z = empty_set
    | Z = successor(empty_set)
    | member(f56(Z),natural_numbers) ) ).

cnf(prime_numbers7,axiom,
    ( member(Z,prime_numbers)
    | ~ member(Z,natural_numbers)
    | Z = empty_set
    | Z = successor(empty_set)
    | apply_to_two_arguments(times,f55(Z),f56(Z)) = Z ) ).

cnf(prime_numbers8,axiom,
    ( member(Z,prime_numbers)
    | ~ member(Z,natural_numbers)
    | Z = empty_set
    | Z = successor(empty_set)
    | ~ member(f55(Z),non_ordered_pair(successor(empty_set),Z)) ) ).

%----Definition of finite
cnf(finite1,axiom,
    ( ~ finite(X)
    | member(f57(X),natural_numbers) ) ).

cnf(finite2,axiom,
    ( ~ finite(X)
    | maps(f58(X),f57(X),X) ) ).

cnf(finite3,axiom,
    ( ~ finite(X)
    | range_of(f58(X)) = X ) ).

cnf(finite4,axiom,
    ( ~ finite(X)
    | one_to_one_function(f58(X)) ) ).

cnf(finite5,axiom,
    ( finite(X)
    | ~ member(Xn,natural_numbers)
    | ~ maps(Xf,Xn,X)
    | range_of(Xf) != X
    | ~ one_to_one_function(Xf) ) ).

%----Definition of twin prime_numbers
cnf(twin_primes1,axiom,
    ( ~ member(Z,twin_prime_numbers)
    | member(Z,prime_numbers) ) ).

cnf(twin_primes2,axiom,
    ( ~ member(Z,twin_prime_numbers)
    | member(successor(successor(Z)),prime_numbers) ) ).

cnf(twin_primes3,axiom,
    ( member(Z,twin_prime_numbers)
    | ~ member(Z,prime_numbers)
    | ~ member(successor(successor(Z)),prime_numbers) ) ).

%----Definition of even_numbers (even natural numbers)
cnf(even_numbers1,axiom,
    ( ~ member(Z,even_numbers)
    | member(Z,natural_numbers) ) ).

cnf(even_numbers2,axiom,
    ( ~ member(Z,even_numbers)
    | member(f59(Z),natural_numbers) ) ).

cnf(even_numbers3,axiom,
    ( ~ member(Z,even_numbers)
    | apply_to_two_arguments(plus,f59(Z),f59(Z)) = Z ) ).

cnf(even_numbers4,axiom,
    ( member(Z,even_numbers)
    | ~ member(Z,natural_numbers)
    | ~ member(X,natural_numbers)
    | apply_to_two_arguments(plus,X,X) != Z ) ).

%--------------------------------------------------------------------------

```

### ./NUM004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : NUM004-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Number Theory (Ordinals)
% Axioms   : Number theory (ordinals) axioms, based on NBG set theory
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Email to G. Sutcliffe
% Source   : [Qua92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   46 (   9 unt;   4 nHn;  40 RR)
%            Number of literals    :  104 (  22 equ;  55 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :   10 (   9 usr;   0 prp; 1-3 aty)
%            Number of functors    :   36 (  36 usr;  12 con; 0-3 aty)
%            Number of variables   :   89 (   8 sgn)
% SPC      : 

% Comments : Requires SET004-0.ax SET004-1.ax
%--------------------------------------------------------------------------
%----Definition of symmetrization of a class.
cnf(symmetrization,axiom,
    union(X,inverse(X)) = symmetrization_of(X) ).

%----could define (irreflexive(x) = (x * ~(identity_relation))).
cnf(irreflexive1,axiom,
    ( ~ irreflexive(X,Y)
    | subclass(restrict(X,Y,Y),complement(identity_relation)) ) ).

cnf(irreflexive2,axiom,
    ( ~ subclass(restrict(X,Y,Y),complement(identity_relation))
    | irreflexive(X,Y) ) ).

%----Definition of connected.
cnf(connected1,axiom,
    ( ~ connected(X,Y)
    | subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X))) ) ).

cnf(connected2,axiom,
    ( ~ subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X)))
    | connected(X,Y) ) ).

%----Definition of transitive.
%----T(x) <--> ((x ^ x) < x).
cnf(transitive1,axiom,
    ( ~ transitive(Xr,Y)
    | subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y)) ) ).

cnf(transitive2,axiom,
    ( ~ subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y))
    | transitive(Xr,Y) ) ).

%----or:
%----transitive(x,y) --> (x < cross_product(V,V)).
%----transitive(x,y) --> ((restrict(x,y,y) ^ restrict(x,y,y)) < x).
%----((restrict(x,y,y) ^ restrict(x,y,y)) < x), (x < cross_product(V,V))
%----    --> transitive(x,y).

%----Definition of asymmetric.
%----asymmetric(x) <--> ((x * inverse(x)) = null_class).
cnf(asymmetric1,axiom,
    ( ~ asymmetric(Xr,Y)
    | restrict(intersection(Xr,inverse(Xr)),Y,Y) = null_class ) ).

cnf(asymmetric2,axiom,
    ( restrict(intersection(Xr,inverse(Xr)),Y,Y) != null_class
    | asymmetric(Xr,Y) ) ).

%----Definition of minimal element.
%----minimum(x,y,z) --> (z e y).
%----minimum(x,y,z) --> (restrict(x,y,{z}) = null_class).
%----(restrict(x,y,{z}) = null_class), (z e y) --> minimum(x,y,z).

%----Definition of segment.
%----If this is useful enough to define, should use it in definition
%----of WE. --> (segment(xr,y,z) = (y * (inverse(xr) image {z}))).
cnf(segment,axiom,
    segment(Xr,Y,Z) = domain_of(restrict(Xr,Y,singleton(Z))) ).

%----Definition of well ordering.
cnf(well_ordering1,axiom,
    ( ~ well_ordering(X,Y)
    | connected(X,Y) ) ).

cnf(well_ordering2,axiom,
    ( ~ well_ordering(Xr,Y)
    | ~ subclass(U,Y)
    | U = null_class
    | member(least(Xr,U),U) ) ).

cnf(well_ordering3,axiom,
    ( ~ well_ordering(Xr,Y)
    | ~ subclass(U,Y)
    | ~ member(V,U)
    | member(least(Xr,U),U) ) ).

cnf(well_ordering4,axiom,
    ( ~ well_ordering(Xr,Y)
    | ~ subclass(U,Y)
    | segment(Xr,U,least(Xr,U)) = null_class ) ).

cnf(well_ordering5,axiom,
    ( ~ well_ordering(Xr,Y)
    | ~ subclass(U,Y)
    | ~ member(V,U)
    | ~ member(ordered_pair(V,least(Xr,U)),Xr) ) ).

cnf(well_ordering6,axiom,
    ( ~ connected(Xr,Y)
    | not_well_ordering(Xr,Y) != null_class
    | well_ordering(Xr,Y) ) ).

cnf(well_ordering7,axiom,
    ( ~ connected(Xr,Y)
    | subclass(not_well_ordering(Xr,Y),Y)
    | well_ordering(Xr,Y) ) ).

cnf(well_ordering8,axiom,
    ( ~ member(V,not_well_ordering(Xr,Y))
    | segment(Xr,not_well_ordering(Xr,Y),V) != null_class
    | ~ connected(Xr,Y)
    | well_ordering(Xr,Y) ) ).

%----Definition of section.
cnf(section1,axiom,
    ( ~ section(Xr,Y,Z)
    | subclass(Y,Z) ) ).

cnf(section2,axiom,
    ( ~ section(Xr,Y,Z)
    | subclass(domain_of(restrict(Xr,Z,Y)),Y) ) ).

%----section(xr,y,z) --> (restrict(xr,z,y) < cross_product(y,y)).
%----section(xr,y,z) --> ((z * (inverse(xr) image y)) < y).

cnf(section3,axiom,
    ( ~ subclass(Y,Z)
    | ~ subclass(domain_of(restrict(Xr,Z,Y)),Y)
    | section(Xr,Y,Z) ) ).

%----Definition of ordinal class.
%----Use (ORD15) to eliminate ordinal_class(x).
%----ordinal_class(x) --> well_ordering(element_relation,x).
%----ordinal_class(x) --> (sum_class(x) < x).
%----well_ordering(element_relation,x), (sum_class(x) < x) -->
%----ordinal_class(x).

%----Definition of ordinal_numbers by Class Existence Theorem.
%----(x e ordinal_numbers) --> ordinal_class(x).
%----(x e V), ordinal_class(x) --> (x e ordinal_numbers).
cnf(ordinal_numbers1,axiom,
    ( ~ member(X,ordinal_numbers)
    | well_ordering(element_relation,X) ) ).

cnf(ordinal_numbers2,axiom,
    ( ~ member(X,ordinal_numbers)
    | subclass(sum_class(X),X) ) ).

cnf(ordinal_numbers3,axiom,
    ( ~ well_ordering(element_relation,X)
    | ~ subclass(sum_class(X),X)
    | ~ member(X,universal_class)
    | member(X,ordinal_numbers) ) ).

cnf(ordinal_numbers4,axiom,
    ( ~ well_ordering(element_relation,X)
    | ~ subclass(sum_class(X),X)
    | member(X,ordinal_numbers)
    | X = ordinal_numbers ) ).

%----(SUCDEF8) Definition of kind_1_ordinals.
cnf(kind_1_ordinals,axiom,
    union(singleton(null_class),image(successor_relation,ordinal_numbers)) = kind_1_ordinals ).

%----(LIMDEF1): definition of limit ordinal.
cnf(limit_ordinals,axiom,
    intersection(complement(kind_1_ordinals),ordinal_numbers) = limit_ordinals ).

%----(TRECDEF1): definition of rest_of by class existence theorem.
%----rest_of(x) ' u = {[u,w] e x : w e V}.
cnf(rest_of1,axiom,
    subclass(rest_of(X),cross_product(universal_class,universal_class)) ).

cnf(rest_of2,axiom,
    ( ~ member(ordered_pair(U,V),rest_of(X))
    | member(U,domain_of(X)) ) ).

cnf(rest_of3,axiom,
    ( ~ member(ordered_pair(U,V),rest_of(X))
    | restrict(X,U,universal_class) = V ) ).

cnf(rest_of4,axiom,
    ( ~ member(U,domain_of(X))
    | restrict(X,U,universal_class) != V
    | member(ordered_pair(U,V),rest_of(X)) ) ).

%----(TRECDEF3.8): definition of rest_relation.
cnf(rest_relation1,axiom,
    subclass(rest_relation,cross_product(universal_class,universal_class)) ).

cnf(rest_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),rest_relation)
    | rest_of(X) = Y ) ).

cnf(rest_relation3,axiom,
    ( ~ member(X,universal_class)
    | member(ordered_pair(X,rest_of(X)),rest_relation) ) ).

%----(TRECDEF4): Definition of Fn = recursion_equation_functions.
%----If z is being used to define a function by transfinite recursion,
%----then Fn(z) is the class of all partial functions that satisfy the
%----recursion equation, for as far out into the ordinals as they are
%----defined.  So THE function defined by z is U Fn(z).
cnf(recursion_equation_functions1,axiom,
    ( ~ member(X,recursion_equation_functions(Z))
    | function(Z) ) ).

cnf(recursion_equation_functions2,axiom,
    ( ~ member(X,recursion_equation_functions(Z))
    | function(X) ) ).

cnf(recursion_equation_functions3,axiom,
    ( ~ member(X,recursion_equation_functions(Z))
    | member(domain_of(X),ordinal_numbers) ) ).

cnf(recursion_equation_functions4,axiom,
    ( ~ member(X,recursion_equation_functions(Z))
    | compose(Z,rest_of(X)) = X ) ).

cnf(recursion_equation_functions5,axiom,
    ( ~ function(Z)
    | ~ function(X)
    | ~ member(domain_of(X),ordinal_numbers)
    | compose(Z,rest_of(X)) != X
    | member(X,recursion_equation_functions(Z)) ) ).

%----(OADEF1): definition of union_of_range_map.
%----Quaife says URAN is the function which maps x into
%----union(range_of(x)).
cnf(union_of_range_map1,axiom,
    subclass(union_of_range_map,cross_product(universal_class,universal_class)) ).

cnf(union_of_range_map2,axiom,
    ( ~ member(ordered_pair(X,Y),union_of_range_map)
    | sum_class(range_of(X)) = Y ) ).

cnf(union_of_range_map3,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | sum_class(range_of(X)) != Y
    | member(ordered_pair(X,Y),union_of_range_map) ) ).

%----(OADEF2): definition of ordinal addition.
cnf(ordinal_addition,axiom,
    apply(recursion(X,successor_relation,union_of_range_map),Y) = ordinal_add(X,Y) ).

%----(OADEF3): definition of twisted plus.
%------> (add_relation < cross_product(ordinal_numbers,cross_product(
%----    ordinal_numbers,ordinal_numbers))).
%----([x,[y,z]] e add_relation) --> (ordinal_add(y,x) = z).
%---- ([y,x] e cross_product(ordinal_numbers,ordinal_numbers)) -->
%----  ([x,[y,ordinal_add(x,y)]] e add_relation).

%----(OMDEF1): definition of ordinal multiplication.
cnf(ordinal_multiplication,axiom,
    recursion(null_class,apply(add_relation,X),union_of_range_map) = ordinal_multiply(X,Y) ).

%----(IADEF1): integer function.
cnf(integer_function1,axiom,
    ( ~ member(X,omega)
    | integer_of(X) = X ) ).

cnf(integer_function2,axiom,
    ( member(X,omega)
    | integer_of(X) = null_class ) ).

%----(IADEF2): integer addition.
%------> (ordinal_add(integer_of(y),integer_of(x)) = (x + y)).

%----(IADEF3): integer multiplication.
%------> (ordinal_multiply(integer_of(y),integer_of(x)) = (x * y)).
%--------------------------------------------------------------------------

```

### ./NUM005+0.ax

```
%------------------------------------------------------------------------------
% File     : NUM005+0 : TPTP v8.2.0. Released v3.1.0.
% Domain   : Number Theory
% Axioms   : Translating from nXXX to rdn notation
% Version  : Especial.
% English  : RDN format is "Reverse Decimal Notation". It stores the digits
%            of a decimal integer in reverse order.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :  256 ( 256 unt;   0 def)
%            Number of atoms       :  256 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :  260 ( 260 usr; 256 con; 0-2 aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(rdn0,axiom,
    rdn_translate(n0,rdn_pos(rdnn(n0))) ).

fof(rdn1,axiom,
    rdn_translate(n1,rdn_pos(rdnn(n1))) ).

fof(rdn2,axiom,
    rdn_translate(n2,rdn_pos(rdnn(n2))) ).

fof(rdn3,axiom,
    rdn_translate(n3,rdn_pos(rdnn(n3))) ).

fof(rdn4,axiom,
    rdn_translate(n4,rdn_pos(rdnn(n4))) ).

... and so on
```

### ./NUM005+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : NUM005+1 : TPTP v8.2.0. Released v3.1.0.
% Domain   : Number Theory
% Axioms   : Less in RDN format
% Version  : Especial.
% English  : Impements a "human style" less using RDN format.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   30 (  18 unt;   0 def)
%            Number of atoms       :   52 (   2 equ)
%            Maximal formula atoms :    4 (   1 avg)
%            Number of connectives :   24 (   2   ~;   1   |;   9   &)
%                                         (   2 <=>;  10  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :   14 (  14 usr;  10 con; 0-2 aty)
%            Number of variables   :   35 (  35   !;   0   ?)
% SPC      : 

% Comments : Requires NUM005+0.ax
%------------------------------------------------------------------------------
fof(rdn_digit1,axiom,
    rdn_non_zero_digit(rdnn(n1)) ).

fof(rdn_digit2,axiom,
    rdn_non_zero_digit(rdnn(n2)) ).

fof(rdn_digit3,axiom,
    rdn_non_zero_digit(rdnn(n3)) ).

fof(rdn_digit4,axiom,
    rdn_non_zero_digit(rdnn(n4)) ).

fof(rdn_digit5,axiom,
    rdn_non_zero_digit(rdnn(n5)) ).

fof(rdn_digit6,axiom,
    rdn_non_zero_digit(rdnn(n6)) ).

fof(rdn_digit7,axiom,
    rdn_non_zero_digit(rdnn(n7)) ).

fof(rdn_digit8,axiom,
    rdn_non_zero_digit(rdnn(n8)) ).

fof(rdn_digit9,axiom,
    rdn_non_zero_digit(rdnn(n9)) ).

fof(rdn_positive_less01,axiom,
    rdn_positive_less(rdnn(n0),rdnn(n1)) ).

fof(rdn_positive_less12,axiom,
    rdn_positive_less(rdnn(n1),rdnn(n2)) ).

fof(rdn_positive_less23,axiom,
    rdn_positive_less(rdnn(n2),rdnn(n3)) ).

fof(rdn_positive_less34,axiom,
    rdn_positive_less(rdnn(n3),rdnn(n4)) ).

fof(rdn_positive_less45,axiom,
    rdn_positive_less(rdnn(n4),rdnn(n5)) ).

fof(rdn_positive_less56,axiom,
    rdn_positive_less(rdnn(n5),rdnn(n6)) ).

fof(rdn_positive_less67,axiom,
    rdn_positive_less(rdnn(n6),rdnn(n7)) ).

fof(rdn_positive_less78,axiom,
    rdn_positive_less(rdnn(n7),rdnn(n8)) ).

fof(rdn_positive_less89,axiom,
    rdn_positive_less(rdnn(n8),rdnn(n9)) ).

fof(rdn_positive_less_transitivity,axiom,
    ! [X,Y,Z] :
      ( ( rdn_positive_less(rdnn(X),rdnn(Y))
        & rdn_positive_less(rdnn(Y),rdnn(Z)) )
     => rdn_positive_less(rdnn(X),rdnn(Z)) ) ).

fof(rdn_positive_less_multi_digit_high,axiom,
    ! [Ds,Os,Db,Ob] :
      ( rdn_positive_less(Os,Ob)
     => rdn_positive_less(rdn(rdnn(Ds),Os),rdn(rdnn(Db),Ob)) ) ).

fof(rdn_positive_less_multi_digit_low,axiom,
    ! [Ds,O,Db] :
      ( ( rdn_positive_less(rdnn(Ds),rdnn(Db))
        & rdn_non_zero(O) )
     => rdn_positive_less(rdn(rdnn(Ds),O),rdn(rdnn(Db),O)) ) ).

fof(rdn_extra_digits_positive_less,axiom,
    ! [D,Db,Ob] :
      ( rdn_non_zero(Ob)
     => rdn_positive_less(rdnn(D),rdn(rdnn(Db),Ob)) ) ).

fof(rdn_non_zero_by_digit,axiom,
    ! [X] :
      ( rdn_non_zero_digit(rdnn(X))
     => rdn_non_zero(rdnn(X)) ) ).

fof(rdn_non_zero_by_structure,axiom,
    ! [D,O] :
      ( rdn_non_zero(O)
     => rdn_non_zero(rdn(rdnn(D),O)) ) ).

fof(less_entry_point_pos_pos,axiom,
    ! [X,Y,RDN_X,RDN_Y] :
      ( ( rdn_translate(X,rdn_pos(RDN_X))
        & rdn_translate(Y,rdn_pos(RDN_Y))
        & rdn_positive_less(RDN_X,RDN_Y) )
     => less(X,Y) ) ).

fof(less_entry_point_neg_pos,axiom,
    ! [X,Y,RDN_X,RDN_Y] :
      ( ( rdn_translate(X,rdn_neg(RDN_X))
        & rdn_translate(Y,rdn_pos(RDN_Y)) )
     => less(X,Y) ) ).

fof(less_entry_point_neg_neg,axiom,
    ! [X,Y,RDN_X,RDN_Y] :
      ( ( rdn_translate(X,rdn_neg(RDN_X))
        & rdn_translate(Y,rdn_neg(RDN_Y))
        & rdn_positive_less(RDN_Y,RDN_X) )
     => less(X,Y) ) ).

fof(less_property,axiom,
    ! [X,Y] :
      ( less(X,Y)
    <=> ( ~ less(Y,X)
        & Y != X ) ) ).

%----Old axiom from the days of natural numbers
%fof(less0,axiom,(
%    ~ ( ? [X] : less(X,n0) )   )).

fof(less_or_equal,axiom,
    ! [X,Y] :
      ( less_or_equal(X,Y)
    <=> ( less(X,Y)
        | X = Y ) ) ).

%----Successive integers
fof(less_successor,axiom,
    ! [X,Y,Z] :
      ( ( sum(X,n1,Y)
        & less(Z,Y) )
     => less_or_equal(Z,X) ) ).

%------------------------------------------------------------------------------

```

### ./NUM005+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : NUM005+2 : TPTP v8.2.0. Released v3.1.0.
% Domain   : Number Theory
% Axioms   : Sum in RDN format
% Version  : Especial.
% English  : Impements a "human style" addition using RDN format.

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :  115 ( 100 unt;   0 def)
%            Number of atoms       :  164 (   3 equ)
%            Maximal formula atoms :    8 (   1 avg)
%            Number of connectives :   49 (   0   ~;   0   |;  34   &)
%                                         (   1 <=>;  14  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   19 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-4 aty)
%            Number of functors    :   14 (  14 usr;  10 con; 0-2 aty)
%            Number of variables   :   86 (  86   !;   0   ?)
% SPC      : 

% Comments : Requires NUM005+0.ax NUM005+1.ax
%------------------------------------------------------------------------------
%----Addition entry points
%----pos(X) + pos(Y)
fof(sum_entry_point_pos_pos,axiom,
    ! [X,Y,Z,RDN_X,RDN_Y,RDN_Z] :
      ( ( rdn_translate(X,rdn_pos(RDN_X))
        & rdn_translate(Y,rdn_pos(RDN_Y))
        & rdn_add_with_carry(rdnn(n0),RDN_X,RDN_Y,RDN_Z)
        & rdn_translate(Z,rdn_pos(RDN_Z)) )
     => sum(X,Y,Z) ) ).

%----neg(X) + neg(Y)
fof(sum_entry_point_neg_neg,axiom,
    ! [X,Y,Z,RDN_X,RDN_Y,RDN_Z] :
      ( ( rdn_translate(X,rdn_neg(RDN_X))
        & rdn_translate(Y,rdn_neg(RDN_Y))
        & rdn_add_with_carry(rdnn(n0),RDN_X,RDN_Y,RDN_Z)
        & rdn_translate(Z,rdn_neg(RDN_Z)) )
     => sum(X,Y,Z) ) ).

%----pos(X) + neg(Y), X < Y
fof(sum_entry_point_pos_neg_1,axiom,
    ! [X,Y,Z,RDN_X,RDN_Y,RDN_Z] :
      ( ( rdn_translate(X,rdn_pos(RDN_X))
        & rdn_translate(Y,rdn_neg(RDN_Y))
        & rdn_positive_less(RDN_X,RDN_Y)
        & rdn_add_with_carry(rdnn(n0),RDN_X,RDN_Z,RDN_Y)
        & rdn_translate(Z,rdn_neg(RDN_Z)) )
     => sum(X,Y,Z) ) ).

%----pos(X) + neg(Y), X > Y
fof(sum_entry_point_pos_neg_2,axiom,
    ! [X,Y,Z,RDN_X,RDN_Y,RDN_Z] :
      ( ( rdn_translate(X,rdn_pos(RDN_X))
        & rdn_translate(Y,rdn_neg(RDN_Y))
        & rdn_positive_less(RDN_Y,RDN_X)
        & rdn_add_with_carry(rdnn(n0),RDN_Y,RDN_Z,RDN_X)
        & rdn_translate(Z,rdn_pos(RDN_Z)) )
     => sum(X,Y,Z) ) ).

%----pos(X) + neg(X), X + -X = n0
fof(sum_entry_point_posx_negx,axiom,
    ! [POS_X,NEG_X,RDN_X] :
      ( ( rdn_translate(POS_X,rdn_pos(RDN_X))
        & rdn_translate(NEG_X,rdn_neg(RDN_X)) )
     => sum(POS_X,NEG_X,n0) ) ).

%----neg + pos
fof(sum_entry_point_neg_pos,axiom,
    ! [X,Y,Z,RDN_X,RDN_Y] :
      ( ( rdn_translate(X,rdn_neg(RDN_X))
        & rdn_translate(Y,rdn_pos(RDN_Y))
        & sum(Y,X,Z) )
     => sum(X,Y,Z) ) ).

%----Sum is unique
fof(unique_sum,axiom,
    ! [X,Y,Z1,Z2] :
      ( ( sum(X,Y,Z1)
        & sum(X,Y,Z2) )
     => Z1 = Z2 ) ).

%----Operands are unique
fof(unique_LHS,axiom,
    ! [X1,X2,Y,Z] :
      ( ( sum(X1,Y,Z)
        & sum(X2,Y,Z) )
     => X1 = X2 ) ).

fof(unique_RHS,axiom,
    ! [X,Y1,Y2,Z] :
      ( ( sum(X,Y1,Z)
        & sum(X,Y2,Z) )
     => Y1 = Y2 ) ).

%----Difference is just sum in reverse
fof(minus_entry_point,axiom,
    ! [X,Y,Z] :
      ( sum(Y,Z,X)
    <=> difference(X,Y,Z) ) ).

%----Addition of positive RDN numbers
fof(add_digit_digit_digit,axiom,
    ! [C,D1,D2,RD,ID] :
      ( ( rdn_digit_add(rdnn(D1),rdnn(D2),rdnn(ID),rdnn(n0))
        & rdn_digit_add(rdnn(ID),rdnn(C),rdnn(RD),rdnn(n0)) )
     => rdn_add_with_carry(rdnn(C),rdnn(D1),rdnn(D2),rdnn(RD)) ) ).

fof(add_digit_digit_rdn,axiom,
    ! [C,D1,D2,ID,RD,IC1,IC2] :
      ( ( rdn_digit_add(rdnn(D1),rdnn(D2),rdnn(ID),rdnn(IC1))
        & rdn_digit_add(rdnn(ID),rdnn(C),rdnn(RD),rdnn(IC2))
        & rdn_digit_add(rdnn(IC1),rdnn(IC2),rdnn(n1),rdnn(n0)) )
     => rdn_add_with_carry(rdnn(C),rdnn(D1),rdnn(D2),rdn(rdnn(RD),rdnn(n1))) ) ).

fof(add_digit_rdn_rdn,axiom,
    ! [C,D1,D2,O2,RD,RO,ID,IC1,IC2,NC] :
      ( ( rdn_digit_add(rdnn(D1),rdnn(D2),rdnn(ID),rdnn(IC1))
        & rdn_digit_add(rdnn(ID),rdnn(C),rdnn(RD),rdnn(IC2))
        & rdn_digit_add(rdnn(IC1),rdnn(IC2),rdnn(NC),rdnn(n0))
        & rdn_add_with_carry(rdnn(NC),rdnn(n0),O2,RO)
        & rdn_non_zero(O2)
        & rdn_non_zero(RO) )
     => rdn_add_with_carry(rdnn(C),rdnn(D1),rdn(rdnn(D2),O2),rdn(rdnn(RD),RO)) ) ).

fof(add_rdn_rdn_rdn,axiom,
    ! [C,D1,O1,D2,O2,RD,RO,ID,IC1,IC2,RC] :
      ( ( rdn_digit_add(rdnn(D1),rdnn(D2),rdnn(ID),rdnn(IC1))
        & rdn_digit_add(rdnn(ID),rdnn(C),rdnn(RD),rdnn(IC2))
        & rdn_digit_add(rdnn(IC1),rdnn(IC2),rdnn(RC),rdnn(n0))
        & rdn_add_with_carry(rdnn(RC),O1,O2,RO)
        & rdn_non_zero(O1)
        & rdn_non_zero(O2)
        & rdn_non_zero(RO) )
     => rdn_add_with_carry(rdnn(C),rdn(rdnn(D1),O1),rdn(rdnn(D2),O2),rdn(rdnn(RD),RO)) ) ).

fof(add_rdn_digit_rdn,axiom,
    ! [C,D1,O1,D2,RD,RO] :
      ( rdn_add_with_carry(rdnn(C),rdnn(D2),rdn(rdnn(D1),O1),rdn(rdnn(RD),RO))
     => rdn_add_with_carry(rdnn(C),rdn(rdnn(D1),O1),rdnn(D2),rdn(rdnn(RD),RO)) ) ).

fof(rdn_digit_add_n0_n0_n0_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n0),rdnn(n0),rdnn(n0)) ).

fof(rdn_digit_add_n0_n1_n1_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n1),rdnn(n1),rdnn(n0)) ).

fof(rdn_digit_add_n0_n2_n2_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n2),rdnn(n2),rdnn(n0)) ).

fof(rdn_digit_add_n0_n3_n3_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n3),rdnn(n3),rdnn(n0)) ).

fof(rdn_digit_add_n0_n4_n4_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n4),rdnn(n4),rdnn(n0)) ).

fof(rdn_digit_add_n0_n5_n5_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n5),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n0_n6_n6_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n6),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n0_n7_n7_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n7),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n0_n8_n8_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n8),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n0_n9_n9_n0,axiom,
    rdn_digit_add(rdnn(n0),rdnn(n9),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n1_n0_n1_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n0),rdnn(n1),rdnn(n0)) ).

fof(rdn_digit_add_n1_n1_n2_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n1),rdnn(n2),rdnn(n0)) ).

fof(rdn_digit_add_n1_n2_n3_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n2),rdnn(n3),rdnn(n0)) ).

fof(rdn_digit_add_n1_n3_n4_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n3),rdnn(n4),rdnn(n0)) ).

fof(rdn_digit_add_n1_n4_n5_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n4),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n1_n5_n6_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n5),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n1_n6_n7_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n6),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n1_n7_n8_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n7),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n1_n8_n9_n0,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n8),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n1_n9_n0_n1,axiom,
    rdn_digit_add(rdnn(n1),rdnn(n9),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n2_n0_n2_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n0),rdnn(n2),rdnn(n0)) ).

fof(rdn_digit_add_n2_n1_n3_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n1),rdnn(n3),rdnn(n0)) ).

fof(rdn_digit_add_n2_n2_n4_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n2),rdnn(n4),rdnn(n0)) ).

fof(rdn_digit_add_n2_n3_n5_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n3),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n2_n4_n6_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n4),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n2_n5_n7_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n5),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n2_n6_n8_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n6),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n2_n7_n9_n0,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n7),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n2_n8_n0_n1,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n8),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n2_n9_n1_n1,axiom,
    rdn_digit_add(rdnn(n2),rdnn(n9),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n3_n0_n3_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n0),rdnn(n3),rdnn(n0)) ).

fof(rdn_digit_add_n3_n1_n4_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n1),rdnn(n4),rdnn(n0)) ).

fof(rdn_digit_add_n3_n2_n5_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n2),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n3_n3_n6_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n3),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n3_n4_n7_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n4),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n3_n5_n8_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n5),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n3_n6_n9_n0,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n6),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n3_n7_n0_n1,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n7),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n3_n8_n1_n1,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n8),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n3_n9_n2_n1,axiom,
    rdn_digit_add(rdnn(n3),rdnn(n9),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n4_n0_n4_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n0),rdnn(n4),rdnn(n0)) ).

fof(rdn_digit_add_n4_n1_n5_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n1),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n4_n2_n6_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n2),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n4_n3_n7_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n3),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n4_n4_n8_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n4),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n4_n5_n9_n0,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n5),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n4_n6_n0_n1,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n6),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n4_n7_n1_n1,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n7),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n4_n8_n2_n1,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n8),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n4_n9_n3_n1,axiom,
    rdn_digit_add(rdnn(n4),rdnn(n9),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n5_n0_n5_n0,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n0),rdnn(n5),rdnn(n0)) ).

fof(rdn_digit_add_n5_n1_n6_n0,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n1),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n5_n2_n7_n0,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n2),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n5_n3_n8_n0,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n3),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n5_n4_n9_n0,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n4),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n5_n5_n0_n1,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n5),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n5_n6_n1_n1,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n6),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n5_n7_n2_n1,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n7),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n5_n8_n3_n1,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n8),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n5_n9_n4_n1,axiom,
    rdn_digit_add(rdnn(n5),rdnn(n9),rdnn(n4),rdnn(n1)) ).

fof(rdn_digit_add_n6_n0_n6_n0,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n0),rdnn(n6),rdnn(n0)) ).

fof(rdn_digit_add_n6_n1_n7_n0,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n1),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n6_n2_n8_n0,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n2),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n6_n3_n9_n0,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n3),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n6_n4_n0_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n4),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n6_n5_n1_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n5),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n6_n6_n2_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n6),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n6_n7_n3_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n7),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n6_n8_n4_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n8),rdnn(n4),rdnn(n1)) ).

fof(rdn_digit_add_n6_n9_n5_n1,axiom,
    rdn_digit_add(rdnn(n6),rdnn(n9),rdnn(n5),rdnn(n1)) ).

fof(rdn_digit_add_n7_n0_n7_n0,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n0),rdnn(n7),rdnn(n0)) ).

fof(rdn_digit_add_n7_n1_n8_n0,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n1),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n7_n2_n9_n0,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n2),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n7_n3_n0_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n3),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n7_n4_n1_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n4),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n7_n5_n2_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n5),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n7_n6_n3_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n6),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n7_n7_n4_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n7),rdnn(n4),rdnn(n1)) ).

fof(rdn_digit_add_n7_n8_n5_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n8),rdnn(n5),rdnn(n1)) ).

fof(rdn_digit_add_n7_n9_n6_n1,axiom,
    rdn_digit_add(rdnn(n7),rdnn(n9),rdnn(n6),rdnn(n1)) ).

fof(rdn_digit_add_n8_n0_n8_n0,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n0),rdnn(n8),rdnn(n0)) ).

fof(rdn_digit_add_n8_n1_n9_n0,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n1),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n8_n2_n0_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n2),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n8_n3_n1_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n3),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n8_n4_n2_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n4),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n8_n5_n3_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n5),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n8_n6_n4_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n6),rdnn(n4),rdnn(n1)) ).

fof(rdn_digit_add_n8_n7_n5_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n7),rdnn(n5),rdnn(n1)) ).

fof(rdn_digit_add_n8_n8_n6_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n8),rdnn(n6),rdnn(n1)) ).

fof(rdn_digit_add_n8_n9_n7_n1,axiom,
    rdn_digit_add(rdnn(n8),rdnn(n9),rdnn(n7),rdnn(n1)) ).

fof(rdn_digit_add_n9_n0_n9_n0,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n0),rdnn(n9),rdnn(n0)) ).

fof(rdn_digit_add_n9_n1_n0_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n1),rdnn(n0),rdnn(n1)) ).

fof(rdn_digit_add_n9_n2_n1_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n2),rdnn(n1),rdnn(n1)) ).

fof(rdn_digit_add_n9_n3_n2_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n3),rdnn(n2),rdnn(n1)) ).

fof(rdn_digit_add_n9_n4_n3_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n4),rdnn(n3),rdnn(n1)) ).

fof(rdn_digit_add_n9_n5_n4_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n5),rdnn(n4),rdnn(n1)) ).

fof(rdn_digit_add_n9_n6_n5_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n6),rdnn(n5),rdnn(n1)) ).

fof(rdn_digit_add_n9_n7_n6_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n7),rdnn(n6),rdnn(n1)) ).

fof(rdn_digit_add_n9_n8_n7_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n8),rdnn(n7),rdnn(n1)) ).

fof(rdn_digit_add_n9_n9_n8_n1,axiom,
    rdn_digit_add(rdnn(n9),rdnn(n9),rdnn(n8),rdnn(n1)) ).

%------------------------------------------------------------------------------

```

### ./NUM006^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : NUM006^0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Number Theory
% Axioms   : Church Numerals in Simple Type Theory
% Version  : [Ben08] axioms : Especial.
% English  :

% Refs     : [Ben08] Benzmueller (2008), Email to G. Sutcliffe
% Source   : [Ben08]
% Names    : CHURCH_NUM [Ben08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   28 (  14 unt;  14 typ;  14 def)
%            Number of atoms       :   14 (  14 equ;   0 cnn)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :   65 (   0   ~;   0   |;   0   &;  65   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  65 nst)
%            Number of types       :    1 (   0 usr)
%            Number of type conns  :   91 (  91   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   15 (  14 usr;   0 con; 2-4 aty)
%            Number of variables   :   33 (  33   ^   0   !;   0   ?;  33   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
thf(zero,type,
    zero: ( $i > $i ) > $i > $i ).

thf(one,type,
    one: ( $i > $i ) > $i > $i ).

thf(two,type,
    two: ( $i > $i ) > $i > $i ).

thf(three,type,
    three: ( $i > $i ) > $i > $i ).

thf(four,type,
    four: ( $i > $i ) > $i > $i ).

thf(five,type,
    five: ( $i > $i ) > $i > $i ).

thf(six,type,
    six: ( $i > $i ) > $i > $i ).

thf(seven,type,
    seven: ( $i > $i ) > $i > $i ).

thf(eight,type,
    eight: ( $i > $i ) > $i > $i ).

thf(nine,type,
    nine: ( $i > $i ) > $i > $i ).

thf(ten,type,
    ten: ( $i > $i ) > $i > $i ).

thf(succ,type,
    succ: ( ( $i > $i ) > $i > $i ) > ( $i > $i ) > $i > $i ).

thf(plus,type,
    plus: ( ( $i > $i ) > $i > $i ) > ( ( $i > $i ) > $i > $i ) > ( $i > $i ) > $i > $i ).

thf(mult,type,
    mult: ( ( $i > $i ) > $i > $i ) > ( ( $i > $i ) > $i > $i ) > ( $i > $i ) > $i > $i ).

thf(zero_ax,definition,
    ( zero
    = ( ^ [X: $i > $i,Y: $i] : Y ) ) ).

thf(one_ax,definition,
    ( one
    = ( ^ [X: $i > $i,Y: $i] : ( X @ Y ) ) ) ).

thf(two_ax,definition,
    ( two
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ Y ) ) ) ) ).

thf(three_ax,definition,
    ( three
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ Y ) ) ) ) ) ).

thf(four_ax,definition,
    ( four
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ).

thf(five_ax,definition,
    ( five
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ).

thf(six_ax,definition,
    ( six
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ) ).

thf(seven_ax,definition,
    ( seven
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ) ) ).

thf(eight_ax,definition,
    ( eight
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ) ) ) ).

thf(nine_ax,definition,
    ( nine
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ) ) ) ) ).

thf(ten_ax,definition,
    ( ten
    = ( ^ [X: $i > $i,Y: $i] : ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ ( X @ Y ) ) ) ) ) ) ) ) ) ) ) ) ).

thf(succ_ax,definition,
    ( succ
    = ( ^ [N: ( $i > $i ) > $i > $i,X: $i > $i,Y: $i] : ( X @ ( N @ X @ Y ) ) ) ) ).

thf(plus_ax,definition,
    ( plus
    = ( ^ [M: ( $i > $i ) > $i > $i,N: ( $i > $i ) > $i > $i,X: $i > $i,Y: $i] : ( M @ X @ ( N @ X @ Y ) ) ) ) ).

thf(mult_ax,definition,
    ( mult
    = ( ^ [M: ( $i > $i ) > $i > $i,N: ( $i > $i ) > $i > $i,X: $i > $i,Y: $i] : ( M @ ( N @ X ) @ Y ) ) ) ).

%------------------------------------------------------------------------------

```

### ./NUM007^0.ax

Very long 1402

### ./NUM007^1.ax

Very long 3304

### ./NUM007^2.ax

Very long 1969

### ./NUM007^3.ax

Very long 2591

### ./NUM007^4.ax

Very long 2769

### ./NUM008+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : NUM008+0 : TPTP v8.2.0. Released v7.3.0.
% Domain   : Number Theory
% Axioms   : Robinson arithmetic with equality
% Version  : Especial.
% English  :

% Refs     : [BBJ03] Boolos et al. (2003), Computability and Logic
%          : [Smi07] Smith (2007), An Introduction to Goedel's Theorems
%          : [Lam18] Lampert (2018), Email to Geoff Sutcliffe
% Source   : [Lam18]
% Names    : 

% Status   : Satisfiable
% Rating   : ? v7.3.0
% Syntax   : Number of formulae    :   11 (   0 unt;   0 def)
%            Number of atoms       :   44 (  17 equ)
%            Maximal formula atoms :    5 (   4 avg)
%            Number of connectives :   47 (  14   ~;  10   |;  23   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   7 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   43 (  23   !;  20   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(axiom_1,axiom,
    ? [Y24] :
    ! [X19] :
      ( ( ~ r1(X19)
        & X19 != Y24 )
      | ( r1(X19)
        & X19 = Y24 ) ) ).

fof(axiom_2,axiom,
    ! [X11] :
    ? [Y21] :
    ! [X12] :
      ( ( ~ r2(X11,X12)
        & X12 != Y21 )
      | ( r2(X11,X12)
        & X12 = Y21 ) ) ).

fof(axiom_3,axiom,
    ! [X13,X14] :
    ? [Y22] :
    ! [X15] :
      ( ( ~ r3(X13,X14,X15)
        & X15 != Y22 )
      | ( r3(X13,X14,X15)
        & X15 = Y22 ) ) ).

fof(axiom_4,axiom,
    ! [X16,X17] :
    ? [Y23] :
    ! [X18] :
      ( ( ~ r4(X16,X17,X18)
        & X18 != Y23 )
      | ( r4(X16,X17,X18)
        & X18 = Y23 ) ) ).

%Axioms of Q

fof(axiom_1a,axiom,
    ! [X1,X8] :
    ? [Y4] :
      ( ? [Y5] :
          ( ? [Y15] :
              ( r2(X8,Y15)
              & r3(X1,Y15,Y5) )
          & Y5 = Y4 )
      & ? [Y7] :
          ( r2(Y7,Y4)
          & r3(X1,X8,Y7) ) ) ).

fof(axiom_2a,axiom,
    ! [X2,X9] :
    ? [Y2] :
      ( ? [Y3] :
          ( ? [Y14] :
              ( r2(X9,Y14)
              & r4(X2,Y14,Y3) )
          & Y3 = Y2 )
      & ? [Y6] :
          ( r3(Y6,X2,Y2)
          & r4(X2,X9,Y6) ) ) ).

fof(axiom_3a,axiom,
    ! [X3,X10] :
      ( ! [Y12] :
          ( ! [Y13] :
              ( ~ r2(X3,Y13)
              | Y13 != Y12 )
          | ~ r2(X10,Y12) )
      | X3 = X10 ) ).

fof(axiom_4a,axiom,
    ! [X4] :
    ? [Y9] :
      ( ? [Y16] :
          ( r1(Y16)
          & r3(X4,Y16,Y9) )
      & Y9 = X4 ) ).

fof(axiom_5a,axiom,
    ! [X5] :
    ? [Y8] :
      ( ? [Y17] :
          ( r1(Y17)
          & r4(X5,Y17,Y8) )
      & ? [Y18] :
          ( r1(Y18)
          & Y8 = Y18 ) ) ).

fof(axiom_6a,axiom,
    ! [X6] :
      ( ? [Y19] :
          ( r1(Y19)
          & X6 = Y19 )
      | ? [Y1,Y11] :
          ( r2(Y1,Y11)
          & X6 = Y11 ) ) ).

fof(axiom_7a,axiom,
    ! [X7,Y10] :
      ( ! [Y20] :
          ( ~ r1(Y20)
          | Y20 != Y10 )
      | ~ r2(X7,Y10) ) ).

%------------------------------------------------------------------------------

```

### ./NUM009+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : NUM009+0 : TPTP v8.2.0. Released v7.3.0.
% Domain   : Number Theory
% Axioms   : Robinson arithmetic without equality
% Version  : Especial.
% English  :

% Refs     : [BBJ03] Boolos et al. (2003), Computability and Logic
%          : [Smi07] Smith (2007), An Introduction to Goedel's Theorems
%          : [Lam18] Lampert (2018), Email to Geoff Sutcliffe
% Source   : [Lam18]
% Names    :

% Status   : Satisfiable
% Rating   : ? v7.3.0
% Syntax   : Number of formulae    :   18 (   1 unt;   0 def)
%            Number of atoms       :   75 (   0 equ)
%            Maximal formula atoms :    7 (   4 avg)
%            Number of connectives :   91 (  34   ~;  26   |;  31   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   8 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   67 (  47   !;  20   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(axiom_1,axiom,
    ? [Y24] :
    ! [X19] :
      ( ( id(X19,Y24)
        & r1(X19) )
      | ( ~ r1(X19)
        & ~ id(X19,Y24) ) ) ).

fof(axiom_2,axiom,
    ! [X11] :
    ? [Y21] :
    ! [X12] :
      ( ( id(X12,Y21)
        & r2(X11,X12) )
      | ( ~ r2(X11,X12)
        & ~ id(X12,Y21) ) ) ).

fof(axiom_3,axiom,
    ! [X13,X14] :
    ? [Y22] :
    ! [X15] :
      ( ( id(X15,Y22)
        & r3(X13,X14,X15) )
      | ( ~ r3(X13,X14,X15)
        & ~ id(X15,Y22) ) ) ).

fof(axiom_4,axiom,
    ! [X16,X17] :
    ? [Y23] :
    ! [X18] :
      ( ( id(X18,Y23)
        & r4(X16,X17,X18) )
      | ( ~ r4(X16,X17,X18)
        & ~ id(X18,Y23) ) ) ).

fof(axiom_5,axiom,
    ! [X20] : id(X20,X20) ).

fof(axiom_6,axiom,
    ! [X21,X22] :
      ( ~ id(X21,X22)
      | id(X22,X21) ) ).

fof(axiom_7,axiom,
    ! [X23,X24,X25] :
      ( ~ id(X23,X24)
      | id(X23,X25)
      | ~ id(X24,X25) ) ).

fof(axiom_8,axiom,
    ! [X26,X27] :
      ( ~ id(X26,X27)
      | ( ~ r1(X26)
        & ~ r1(X27) )
      | ( r1(X26)
        & r1(X27) ) ) ).

fof(axiom_9,axiom,
    ! [X28,X29,X30,X31] :
      ( ~ id(X28,X30)
      | ~ id(X29,X31)
      | ( ~ r2(X28,X29)
        & ~ r2(X30,X31) )
      | ( r2(X28,X29)
        & r2(X30,X31) ) ) ).

fof(axiom_10,axiom,
    ! [X32,X33,X34,X35,X36,X37] :
      ( ~ id(X32,X35)
      | ~ id(X33,X36)
      | ~ id(X34,X37)
      | ( ~ r3(X32,X33,X34)
        & ~ r3(X35,X36,X37) )
      | ( r3(X32,X33,X34)
        & r3(X35,X36,X37) ) ) ).

fof(axiom_11,axiom,
    ! [X38,X39,X40,X41,X42,X43] :
      ( ~ id(X38,X41)
      | ~ id(X39,X42)
      | ~ id(X40,X43)
      | ( ~ r4(X38,X39,X40)
        & ~ r4(X41,X42,X43) )
      | ( r4(X38,X39,X40)
        & r4(X41,X42,X43) ) ) ).

%----Axioms of Q
fof(axiom_1a,axiom,
    ! [X1,X8] :
    ? [Y4] :
      ( ? [Y5] :
          ( id(Y5,Y4)
          & ? [Y15] :
              ( r2(X8,Y15)
              & r3(X1,Y15,Y5) ) )
      & ? [Y7] :
          ( r2(Y7,Y4)
          & r3(X1,X8,Y7) ) ) ).

fof(axiom_2a,axiom,
    ! [X2,X9] :
    ? [Y2] :
      ( ? [Y3] :
          ( id(Y3,Y2)
          & ? [Y14] :
              ( r2(X9,Y14)
              & r4(X2,Y14,Y3) ) )
      & ? [Y6] :
          ( r3(Y6,X2,Y2)
          & r4(X2,X9,Y6) ) ) ).

fof(axiom_3a,axiom,
    ! [X3,X10] :
      ( ! [Y12] :
          ( ! [Y13] :
              ( ~ id(Y13,Y12)
              | ~ r2(X3,Y13) )
          | ~ r2(X10,Y12) )
      | id(X3,X10) ) ).

fof(axiom_4a,axiom,
    ! [X4] :
    ? [Y9] :
      ( id(Y9,X4)
      & ? [Y16] :
          ( r1(Y16)
          & r3(X4,Y16,Y9) ) ) ).

fof(axiom_5a,axiom,
    ! [X5] :
    ? [Y8] :
      ( ? [Y17] :
          ( r1(Y17)
          & r4(X5,Y17,Y8) )
      & ? [Y18] :
          ( id(Y8,Y18)
          & r1(Y18) ) ) ).

fof(axiom_6a,axiom,
    ! [X6] :
      ( ? [Y19] :
          ( id(X6,Y19)
          & r1(Y19) )
      | ? [Y1,Y11] :
          ( id(X6,Y11)
          & r2(Y1,Y11) ) ) ).

fof(axiom_7a,axiom,
    ! [X7,Y10] :
      ( ! [Y20] :
          ( ~ id(Y20,Y10)
          | ~ r1(Y20) )
      | ~ r2(X7,Y10) ) ).

%------------------------------------------------------------------------------

```

## Philosophy

### ./PHI001^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : PHI001^0 : TPTP v8.2.0. Released v6.1.0.
% Domain   : Philosophy
% Axioms   : Axioms for Goedel's Ontological Proof of the Existence of God
% Version  : [Ben13] axioms.
% English  :

% Refs     : [Ben13] Benzmueller (2009), Email to Geoff Sutcliffe
% Source   : [Ben13]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   12 (   3 unt;   4 typ;   3 def)
%            Number of atoms       :   49 (   3 equ;   0 cnn)
%            Maximal formula atoms :   10 (   4 avg)
%            Number of connectives :   61 (   0   ~;   0   |;   0   &;  61   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   15 (   5 avg;  61 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   29 (  29   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   15 (  14 usr;  10 con; 0-3 aty)
%            Number of variables   :   15 (  15   ^   0   !;   0   ?;  15   :)
% SPC      : TH0_SAT_EQU

% Comments : Requires LCL016^0.ax
%------------------------------------------------------------------------------
%----Signature
thf(positive_tp,type,
    positive: ( mu > $i > $o ) > $i > $o ).

thf(god_tp,type,
    god: mu > $i > $o ).

%----Constant symbol for essence: ess
thf(essence_tp,type,
    essence: ( mu > $i > $o ) > mu > $i > $o ).

%----Constant symbol for necessary existence: ne
thf(necessary_existence_tp,type,
    necessary_existence: mu > $i > $o ).

%----A1: Either the property or its negation are positive, but not both.
%----(Remark: only the left to right is needed for proving T1)
thf(axA1,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mequiv
          @ ( positive
            @ ^ [X: mu] : ( mnot @ ( Phi @ X ) ) )
          @ ( mnot @ ( positive @ Phi ) ) ) ) ) ).

%----A2: A property necessarily implied by a positive property is positive.
thf(axA2,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mforall_indset
          @ ^ [Psi: mu > $i > $o] :
              ( mimplies
              @ ( mand @ ( positive @ Phi )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [X: mu] : ( mimplies @ ( Phi @ X ) @ ( Psi @ X ) ) ) ) )
              @ ( positive @ Psi ) ) ) ) ) ).

%----D1: A God-like being possesses all positive properties.
thf(defD1,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] : ( mimplies @ ( positive @ Phi ) @ ( Phi @ X ) ) ) ) ) ).

%----A3: The property of being God-like is positive.
thf(axA3,axiom,
    mvalid @ ( positive @ god ) ).

%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] : ( mimplies @ ( positive @ Phi ) @ ( mbox @ ( positive @ Phi ) ) ) ) ) ).

%----D2: An essence of an individual is a property possessed by it and
%----necessarily implying any of its properties.
thf(defD2,definition,
    ( essence
    = ( ^ [Phi: mu > $i > $o,X: mu] :
          ( mand @ ( Phi @ X )
          @ ( mforall_indset
            @ ^ [Psi: mu > $i > $o] :
                ( mimplies @ ( Psi @ X )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [Y: mu] : ( mimplies @ ( Phi @ Y ) @ ( Psi @ Y ) ) ) ) ) ) ) ) ) ).

%----D3: Necessary existence of an entity is the exemplification of all its 
%----essences.
thf(defD3,definition,
    ( necessary_existence
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( essence @ Phi @ X )
              @ ( mbox
                @ ( mexists_ind
                  @ ^ [Y: mu] : ( Phi @ Y ) ) ) ) ) ) ) ).

%----A5: Necessary existence is positive.
thf(axA5,axiom,
    mvalid @ ( positive @ necessary_existence ) ).

%------------------------------------------------------------------------------

```

### ./PHI002+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : PHI002+0 : TPTP v8.2.0. Released v7.4.0.
% Domain   : Philosophy
% Axioms   : Definitions for Spinoza's Ethics - the DAPI
% Version  : [Hor19] axioms.
% English  :

% Refs     : [Hor19] Horner (2019), A Computationally Assisted Reconstructi
%            [Hor20] Horner (2020), Email to Geoff Sutcliffe
% Source   : [Hor20]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   10 (   0 unt;   0 def)
%            Number of atoms       :   37 (   0 equ)
%            Maximal formula atoms :    6 (   3 avg)
%            Number of connectives :   27 (   0   ~;   2   |;  13   &)
%                                         (  10 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   5 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   34 (  34 usr;   0 prp; 1-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   16 (  16   !;   0   ?)
% SPC      : FOF_SAT_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
%----Definition I. Self-caused. By that which is self-caused, I mean that of
%----which the essence involves existence, or that of which the nature
%----conceivable as existent. Note that "or" in the "... or that of which the
%----nature ..." must be rendered as "&" to capture what Spinoza means.
fof(self_caused,axiom,
    ! [X] :
      ( selfCaused(X)
    <=> ( essenceInvExistence(X)
        & natureConcOnlyByExistence(X) ) ) ).

%----Definition II. Finite after its kind. A thing finite after its kind, when
%----it can be limited by another thing of the same nature.
fof(finite_after_its_kind,axiom,
    ! [X,Y] :
      ( finiteAfterItsKind(X)
    <=> ( canBeLimitedBy(X,Y)
        & sameKind(X,Y) ) ) ).

%----Definition III. Substance. By substance, I mean that which is in itself,
%----and is conceived through itself.
fof(substance,axiom,
    ! [X] :
      ( substance(X)
    <=> ( inItself(X)
        & conceivedThruItself(X) ) ) ).

%----Definition IV. Attribute. By attribute, I mean that which the intellect
%----perceives as constituting the essence of substance.
fof(attribute,axiom,
    ! [X] :
      ( attribute(X)
    <=> intPercAsConstEssSub(X) ) ).

%----Definition V. Mode. By mode, I mean the modifications of substance, or
%----that which exists in, and is conceived through, something other than
%----itself.
fof(mode,axiom,
    ! [X,Y,Z] :
      ( mode(X)
    <=> ( ( modification(X,Y)
          & substance(Y) )
        | ( existsIn(X,Z)
          & conceivedThru(X,Z) ) ) ) ).

%----Definition VI. God. By God, I mean a being absolutely infinite.
fof(god,axiom,
    ! [X] :
      ( god(X)
    <=> ( being(X)
        & absolutelyInfinite(X) ) ) ).

%----Definition VI. Absolutely infinite. ... that is, a substance consisting 
%----in infinite attributes, of which each expresses eternal and infinite 
%----essentiality. 
fof(absolutely_infinite,axiom,
    ! [X,Y] :
      ( absolutelyInfinite(X)
    <=> ( substance(X)
        & constInInfAttributes(X)
        & ( attributeOf(Y,X)
         => ( expressesEternalEssentiality(Y)
            & expressesInfiniteEssentiality(Y) ) ) ) ) ).

%----Definition VII. Free. That thing is called free, which exists solely by 
%----the necessity of its own nature, and of which the action is determined 
%----by itself alone.
fof(free,axiom,
    ! [X,Y] :
      ( free(X)
    <=> ( existsOnlyByNecessityOfOwnNature(X)
        & ( actionOf(Y,X)
         => determinedByItselfAlone(Y,X) ) ) ) ).

%----Definition VII. Necessary. ... that thing is necessary, or rather 
%----constrained, which is by something external to itself to a fixed and 
%----definite method of existence or action.
fof(necessary,axiom,
    ! [X,Y] :
      ( necessary(X)
    <=> ( externalTo(Y,X)
        & determinedByFixedMethod(X,Y)
        & determinedByDefiniteMethod(X,Y)
        & ( isMethodAction(Y)
          | isMethodExistence(Y) ) ) ) ).

%----Definition VIII. Eternity. By eternity, I mean existence itself, in so 
%----far as it is conceived necessarily to follow solely from the definition 
%----of that which is eternal.
fof(eternity,axiom,
    ! [X] :
      ( eternity(X)
    <=> existConcFollowFromDefEternal(X) ) ).

%------------------------------------------------------------------------------

```

### ./PHI002+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : PHI002+1 : TPTP v8.2.0. Released v7.4.0.
% Domain   : Philosophy
% Axioms   : Axioms for Spinoza's Ethics - the DAPI
% Version  : [Hor19] axioms.
% English  :

% Refs     : [Hor19] Horner (2019), A Computationally Assisted Reconstructi
%            [Hor20] Horner (2020), Email to Geoff Sutcliffe
% Source   : [Hor20]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    7 (   0 unt;   0 def)
%            Number of atoms       :   24 (   2 equ)
%            Maximal formula atoms :    5 (   3 avg)
%            Number of connectives :   27 (  10   ~;   2   |;   7   &)
%                                         (   2 <=>;   6  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   6 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   17 (  16 usr;   0 prp; 1-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   13 (  13   !;   0   ?)
% SPC      : FOF_SAT_RFO_SEQ

% Comments : Requires PHI002+0.ax
%------------------------------------------------------------------------------
%----Axiom I. Everything which exists, exists either in itself or in something 
%----else.
fof(exists,axiom,
    ! [X,Y] :
      ( exists(X)
    <=> ( existsIn(X,X)
        | ( existsIn(X,Y)
          & X != Y ) ) ) ).

%----Axiom II. That which cannot be conceived through itself must be conceived 
%----through something else.
fof(conceived_through,axiom,
    ! [X,Y] :
      ( ~ conceivedThru(X,X)
     => ( conceivedThru(X,Y)
        & X != Y ) ) ).

%----Axiom III. From a given definite cause an effect necessarily follows; 
%----and, on the other hand, if no definite cause be granted, it is impossible 
%----that an effect can follow.
fof(definite_cause,axiom,
    ! [X,Y] :
      ( definiteCause(X)
     => ( effectNecessarilyFollowsFrom(Y,X)
        & ( ~ definiteCause(X)
         => ~ effectNecessarilyFollowsFrom(Y,X) ) ) ) ).

%----Axiom IV. The knowledge of an effect depends on and involves the knowledge 
%----of a cause. 
fof(knowledge_of_effect,axiom,
    ! [X,Y] :
      ( knowledgeOfEffect(X,Y)
    <=> knowledgeOfACause(X) ) ).

%----Axiom V. Things which have nothing in common cannot be understood, the 
%----one by the means of the other the one by means of the other; the 
%----conception of one does not involve the conception of the other. 
fof(have_nothing_in_common,axiom,
    ! [X,Y] :
      ( haveNothingInCommon(X,Y)
     => ( ~ canBeUnderstoodInTermsOf(X,Y)
        & ~ canBeUnderstoodInTermsOf(Y,X)
        & ~ conceptionInvolves(X,Y)
        & ~ conceptionInvolves(Y,X) ) ) ).

%----Axiom VI. A true idea must correspond with its ideate or object. 
fof(true_idea,axiom,
    ! [X,Y] :
      ( trueIdea(X)
     => ( correspondWith(X,Y)
        & ( ideateOf(Y,X)
          | objectOf(Y,X) ) ) ) ).

%----Axiom VII. If a thing can be conceived as non-existing, its essence does 
%----not involve its existence. 
fof(can_be_conceived_as_non_existing,axiom,
    ! [X] :
      ( canBeConceivedAsNonExisting(X)
     => ~ essenceInvExistence(X) ) ).

%------------------------------------------------------------------------------

```

## Planning

### ./PLA001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : PLA001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Planning (Blocks world)
% Axioms   : Blocks world axioms
% Version  : [SE94] axioms.
% English  :

% Refs     : [Sus73] Sussman (1973), A Computational Model of Skill Acquisi
%          : [SE94]  Segre & Elkan (1994), A High-Performance Explanation-B
% Source   : [SE94]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   10 (   0 unt;   0 nHn;   8 RR)
%            Number of literals    :   31 (   0 equ;  21 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    9 (   9 usr;   2 con; 0-2 aty)
%            Number of variables   :   33 (   3 sgn)
% SPC      : 

% Comments : The axioms are a reconstruction of the situation calculus
%            blocks world as in [Sus73].
%--------------------------------------------------------------------------
cnf(and_definition,axiom,
    ( holds(and(X,Y),State)
    | ~ holds(X,State)
    | ~ holds(Y,State) ) ).

cnf(pickup_1,axiom,
    ( holds(holding(X),do(pickup(X),State))
    | ~ holds(empty,State)
    | ~ holds(clear(X),State)
    | ~ differ(X,table) ) ).

cnf(pickup_2,axiom,
    ( holds(clear(Y),do(pickup(X),State))
    | ~ holds(on(X,Y),State)
    | ~ holds(clear(X),State)
    | ~ holds(empty,State) ) ).

cnf(pickup_3,axiom,
    ( holds(on(X,Y),do(pickup(Z),State))
    | ~ holds(on(X,Y),State)
    | ~ differ(X,Z) ) ).

cnf(pickup_4,axiom,
    ( holds(clear(X),do(pickup(Z),State))
    | ~ holds(clear(X),State)
    | ~ differ(X,Z) ) ).

cnf(putdown_1,axiom,
    ( holds(empty,do(putdown(X,Y),State))
    | ~ holds(holding(X),State)
    | ~ holds(clear(Y),State) ) ).

cnf(putdown_2,axiom,
    ( holds(on(X,Y),do(putdown(X,Y),State))
    | ~ holds(holding(X),State)
    | ~ holds(clear(Y),State) ) ).

cnf(putdown_3,axiom,
    ( holds(clear(X),do(putdown(X,Y),State))
    | ~ holds(holding(X),State)
    | ~ holds(clear(Y),State) ) ).

cnf(putdown_4,axiom,
    ( holds(on(X,Y),do(putdown(Z,W),State))
    | ~ holds(on(X,Y),State) ) ).

cnf(putdown_5,axiom,
    ( holds(clear(Z),do(putdown(X,Y),State))
    | ~ holds(clear(Z),State)
    | ~ differ(Z,Y) ) ).

%--------------------------------------------------------------------------

```

### ./PLA001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : PLA001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Planning (Blocks world)
% Axioms   : Blocks world difference axioms for 4 blocks
% Version  : [SE94] axioms.
% English  :

% Refs     : [Sus73] Sussman (1973), A Computational Model of Skill Acquisi
%          : [SE94]  Segre & Elkan (1994), A High-Performance Explanation-B
% Source   : [SE94]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   20 (  19 unt;   0 nHn;  19 RR)
%            Number of literals    :   21 (   0 equ;   1 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    9 (   9 usr;   7 con; 0-2 aty)
%            Number of variables   :    3 (   1 sgn)
% SPC      : 

% Comments : Requires PLA001-0.ax
%          : The axioms are a reconstruction of the situation calculus
%            blocks world as in [Sus73].
%--------------------------------------------------------------------------
cnf(symmetry_of_differ,axiom,
    ( differ(X,Y)
    | ~ differ(Y,X) ) ).

cnf(differ_a_b,axiom,
    differ(a,b) ).

cnf(differ_a_c,axiom,
    differ(a,c) ).

cnf(differ_a_d,axiom,
    differ(a,d) ).

cnf(differ_a_table,axiom,
    differ(a,table) ).

cnf(differ_b_c,axiom,
    differ(b,c) ).

cnf(differ_b_d,axiom,
    differ(b,d) ).

cnf(differ_b_table,axiom,
    differ(b,table) ).

cnf(differ_c_d,axiom,
    differ(c,d) ).

cnf(differ_c_table,axiom,
    differ(c,table) ).

cnf(differ_d_table,axiom,
    differ(d,table) ).

%----Initial configuration
cnf(initial_state1,axiom,
    holds(on(a,table),s0) ).

cnf(initial_state2,axiom,
    holds(on(b,table),s0) ).

cnf(initial_state3,axiom,
    holds(on(c,d),s0) ).

cnf(initial_state4,axiom,
    holds(on(d,table),s0) ).

cnf(initial_state5,axiom,
    holds(clear(a),s0) ).

cnf(initial_state6,axiom,
    holds(clear(b),s0) ).

cnf(initial_state7,axiom,
    holds(clear(c),s0) ).

cnf(initial_state8,axiom,
    holds(empty,s0) ).

%----Table is always clear
cnf(clear_table,axiom,
    holds(clear(table),State) ).

%--------------------------------------------------------------------------

```

### ./PLA002+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : PLA002+0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Planning (Blocks world)
% Axioms   : Blocks world axioms
% Version  : [Bau99] axioms.
% English  :

% Refs     : [Bau99] Baumgartner (1999), FTP'2000 - Problem Sets
%            [KS96]  Kautz & Selman (1996), Pushing the Envelope: Planning,
%            [KS92]  Kautz & Selman (1992), Planning as Satisfiability
% Source   : [Bau99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   24 (   0 unt;   0 def)
%            Number of atoms       :  119 (   0 equ)
%            Maximal formula atoms :    8 (   4 avg)
%            Number of connectives :  120 (  25   ~;   0   |;  43   &)
%                                         (   0 <=>;  52  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   8 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 1-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :   64 (  64   !;   0   ?)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
% blocks_axioms:
fof(place_object_block_on_destination,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Z] :
          ( ( a_block(Z)
            & neq(X,Z) )
         => ( ( time(I)
              & object(X,I)
              & destination(Z,I) )
           => on(X,Z,s(I)) ) ) ) ).

% All( x, block, ! member( x, fixed),
%     All( y, block, ! eql( x, y),
%  Disj(
%       Not( L2("object",  x, i));
%       Not( L2("source", y, i));
%       Not( L3("on", x, y, 1 + i)))));
fof(remove_object_block_from_source,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Y] :
          ( ( a_block(Y)
            & neq(X,Y) )
         => ( ( time(I)
              & object(X,I)
              & source(Y,I) )
           => ~ on(X,Y,s(I)) ) ) ) ).

% All( y, block, ! member( y, fixed),
%     Disj(
%   Not( L2("source", y, i));
%   L2("clear", y, 1 + i);
%   ));
fof(clear_source_after_removal,axiom,
    ! [I,Y] :
      ( nonfixed(Y)
     => ( ( time(I)
          & source(Y,I) )
       => clear(Y,s(I)) ) ) ).

% All( z, block, ! member( z, fixed),
%     Disj(
%   Not( L2("destination", z, i));
%   Not( L2("clear", z, 1 + i))));
fof(not_clear_destination_after_placement,axiom,
    ! [I,Z] :
      ( nonfixed(Z)
     => ( ( time(I)
          & destination(Z,I) )
       => ~ clear(Z,s(I)) ) ) ).

fof(object_block_on_source,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Y] :
          ( ( a_block(Y)
            & neq(X,Y) )
         => ( ( object(X,I)
              & source(Y,I) )
           => on(X,Y,I) ) ) ) ).

% All( x, block, ! member( x, fixed),
%     Disj(
%   Not( L2("object",  x, i));
%   L2("clear", x, i)));
fof(object_block_is_clear,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ( object(X,I)
       => clear(X,I) ) ) ).

% All( z, block, ! member( z, fixed),
%     Disj(
%   Not( L2("destination", z, i));
%   L2("clear", z, i)));
fof(destination_block_is_clear,axiom,
    ! [I,Z] :
      ( nonfixed(Z)
     => ( destination(Z,I)
       => clear(Z,I) ) ) ).

fof(non_destination_remains_clear,axiom,
    ! [I,W] :
      ( nonfixed(W)
     => ( ( time(I)
          & ~ destination(W,I)
          & clear(W,I) )
       => clear(W,s(I)) ) ) ).

% All( v, block, ! member( v, fixed),
%     All( w, block, !eql( v, w),
%  Disj(
%       L2("object",  v, i);
%       Not( L3("on", v, w, i)) ;
%       L3("on", v, w, 1 + i))));
fof(non_object_remains_on,axiom,
    ! [I,V] :
      ( nonfixed(V)
     => ! [W] :
          ( ( a_block(W)
            & neq(V,W) )
         => ( ( time(I)
              & ~ object(V,I)
              & on(V,W,I) )
           => on(V,W,s(I)) ) ) ) ).

fof(non_source_remains_not_clear,axiom,
    ! [I,W] :
      ( nonfixed(W)
     => ( ( time(I)
          & ~ source(W,I)
          & ~ clear(W,I) )
       => ~ clear(W,s(I)) ) ) ).

% All( v, block, ! member( v, fixed),
%     All( w, block, ! eql( v, w),
%  Disj(
%       L2("object",  v, i);
%       L3("on", v, w, i) ;
%       Not( L3("on", v, w, 1 + i)))));
fof(non_object_remains_not_on,axiom,
    ! [I,V] :
      ( nonfixed(V)
     => ! [W] :
          ( ( a_block(W)
            & neq(V,W) )
         => ( ( time(I)
              & ~ object(V,I)
              & ~ on(V,W,I) )
           => ~ on(V,W,s(I)) ) ) ) ).

% All( v, block, ! member( v, fixed),
%     All( w, block, ! eql( v, w),
%  Disj(
%       L2("destination", w, i);
%       L3("on", v, w, i);
%       Not( L3("on", v, w, 1 + i)))));
fof(non_destination_remains_not_on,axiom,
    ! [I,V] :
      ( nonfixed(V)
     => ! [W] :
          ( ( a_block(W)
            & neq(V,W) )
         => ( ( time(I)
              & ~ destination(W,I)
              & ~ on(V,W,I) )
           => ~ on(V,W,s(I)) ) ) ) ).

fof(only_one_object_block,axiom,
    ! [I,X1] :
      ( nonfixed(X1)
     => ! [X2] :
          ( ( a_block(X2)
            & neq(X1,X2) )
         => ~ ( object(X1,I)
              & object(X2,I) ) ) ) ).

% All( y1, block, 1,
%     All( y2, block, ! eql( y1, y2),
%  Disj(
%       Not( L2("source", y1, i));
%       Not( L2("source", y2, i)))));
fof(only_one_source_block,axiom,
    ! [I,Y1] :
      ( a_block(Y1)
     => ! [Y2] :
          ( ( a_block(Y2)
            & neq(Y1,Y2) )
         => ~ ( source(Y1,I)
              & source(Y2,I) ) ) ) ).

% All( z1, block, 1,
%     All( z2, block, ! eql( z1, z2),
%  Disj(
%       Not( L2("destination", z1, i));
%       Not( L2("destination", z2, i)))));
fof(only_one_destination_block,axiom,
    ! [I,Z1] :
      ( a_block(Z1)
     => ! [Z2] :
          ( ( a_block(Z2)
            & neq(Z1,Z2) )
         => ~ ( destination(Z1,I)
              & destination(Z2,I) ) ) ) ).

fof(object_is_not_source,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ~ ( object(X,I)
          & source(X,I) ) ) ).

% All( x, block, ! member( x, fixed),
%     Disj(
%   Not( L2("object",  x, i));
%   Not( L2("destination", x, i))));
fof(object_is_not_destination,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ~ ( object(X,I)
          & destination(X,I) ) ) ).

% All( y, block, y,
%     Disj(
%   Not( L2("source", y, i));
%   Not( L2("destination", y, i))));
fof(source_is_not_destination,axiom,
    ! [I,Y] :
      ( a_block(Y)
     => ~ ( source(Y,I)
          & destination(Y,I) ) ) ).

%% on_axioms:
fof(not_on_each_other,axiom,
    ! [I,X] :
      ( a_block(X)
     => ! [Y] :
          ( ( a_block(Y)
            & neq(X,Y) )
         => ~ ( on(X,Y,I)
              & on(Y,X,I) ) ) ) ).

fof(not_on_self,axiom,
    ! [I,X] :
      ( a_block(X)
     => ~ on(X,X,I) ) ).

fof(only_one_on,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Y] :
          ( ( nonfixed(Y)
            & neq(X,Y) )
         => ! [Z] :
              ( ( nonfixed(Z)
                & neq(X,Z)
                & neq(Y,Z) )
             => ~ ( on(X,Y,I)
                  & on(Z,Y,I) ) ) ) ) ).

fof(only_on_one_thing,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Y] :
          ( ( a_block(Y)
            & neq(X,Y) )
         => ! [Z] :
              ( ( a_block(Z)
                & neq(X,Z)
                & neq(Y,Z) )
             => ~ ( on(X,Y,I)
                  & on(X,Z,I) ) ) ) ) ).

fof(not_clear_if_something_on,axiom,
    ! [I,X] :
      ( nonfixed(X)
     => ! [Y] :
          ( nonfixed(Y)
         => ~ ( on(X,Y,I)
              & clear(Y,I) ) ) ) ).

fof(fixed_not_on_anything,axiom,
    ! [I,X] :
      ( a_block(X)
     => ! [Y] :
          ( fixed(Y)
         => ~ on(Y,X,I) ) ) ).

%--------------------------------------------------------------------------

```

### ./PRD001+0.ax

Very long 7340

## Puzzles

### ./PUZ001-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : PUZ001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Puzzles (Mars and Venus)
% Axioms   : Mars and Venus axioms
% Version  :
% English  :

% Refs     : [Rap95] Raptis (1995), Email to G. Sutcliffe
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   16 (   0 unt;   4 nHn;  12 RR)
%            Number of literals    :   39 (   1 equ;  23 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    9 (   8 usr;   0 prp; 1-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 1-1 aty)
%            Number of variables   :   20 (   1 sgn)
% SPC      : 

% Comments : [Rap95] has pointed out that the clause
%            statements_are_true_or_not is a tautology. Does your ATP
%            system ignore it?
%------------------------------------------------------------------------------
%----Everyone's either from Mars or Venus, male or female, and statements
%----are true or false
cnf(from_mars_or_venus,axiom,
    ( from_mars(X)
    | from_venus(X) ) ).

cnf(not_from_mars_and_venus,axiom,
    ( ~ from_mars(X)
    | ~ from_venus(X) ) ).

cnf(male_or_female,axiom,
    ( male(X)
    | female(X) ) ).

cnf(not_male_and_female,axiom,
    ( ~ male(X)
    | ~ female(X) ) ).

cnf(truthteller_or_liar,axiom,
    ( truthteller(X)
    | liar(X) ) ).

cnf(not_truthteller_and_liar,axiom,
    ( ~ truthteller(X)
    | ~ liar(X) ) ).

%----Rules about statements
cnf(statements_are_true_or_not,axiom,
    ( ~ says(X,Y)
    | a_truth(Y)
    | ~ a_truth(Y) ) ).

cnf(people_say_their_statements,axiom,
    ( ~ says(X,Y)
    | Y = statement_by(X) ) ).

cnf(true_statements_made_by_truthtellers,axiom,
    ( ~ a_truth(statement_by(X))
    | truthteller(X) ) ).

cnf(false_statements_made_by_liars,axiom,
    ( a_truth(statement_by(X))
    | liar(X) ) ).

%----Who's a liar, who's not
cnf(venusian_female_are_truthtellers,axiom,
    ( ~ from_venus(X)
    | ~ female(X)
    | truthteller(X) ) ).

cnf(venusian_males_are_liars,axiom,
    ( ~ from_venus(X)
    | ~ male(X)
    | liar(X) ) ).

cnf(marsian_males_are_truthtellers,axiom,
    ( ~ from_mars(X)
    | ~ male(X)
    | truthteller(X) ) ).

cnf(marsian_females_are_liars,axiom,
    ( ~ from_mars(X)
    | ~ female(X)
    | liar(X) ) ).

%----what truthtellers say is true, what liars say is false, what
%----truthtellers say is true, what liars say is false
cnf(truthtellers_make_true_statements,axiom,
    ( ~ truthteller(X)
    | ~ says(X,Y)
    | a_truth(Y) ) ).

cnf(liars_make_false_statements,axiom,
    ( ~ liar(X)
    | ~ says(X,Y)
    | ~ a_truth(Y) ) ).

%------------------------------------------------------------------------------

```

### ./PUZ002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : PUZ002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Puzzles (Truthtellers and Liars)
% Axioms   : Truthtellers and Liars axioms for two types of people
% Version  : [LO85] axioms.
% English  : Axioms for two types of people; truthtellers and liars.

% Refs     : [Smu78] Smullyan (1978), What is the name of this book?-The ri
%          : [LO85]  Lusk & Overbeek (1985), Non-Horn Problems
% Source   : [LO85]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   2 nHn;   5 RR)
%            Number of literals    :   16 (   0 equ;  10 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(truthteller_or_liar,axiom,
    ( a_truth(truthteller(X))
    | a_truth(liar(X)) ) ).

cnf(not_both,axiom,
    ( ~ a_truth(truthteller(X))
    | ~ a_truth(liar(X)) ) ).

cnf(truthtellers_tell_truth,axiom,
    ( ~ a_truth(truthteller(Truthteller))
    | ~ a_truth(says(Truthteller,Statement))
    | a_truth(Statement) ) ).

cnf(liars_lie,axiom,
    ( ~ a_truth(liar(Liar))
    | ~ a_truth(says(Liar,Statement))
    | ~ a_truth(Statement) ) ).

cnf(truths_are_told_by_truthtellers,axiom,
    ( ~ a_truth(Statement)
    | ~ a_truth(says(Truthteller,Statement))
    | a_truth(truthteller(Truthteller)) ) ).

cnf(liars_are_told_by_liars,axiom,
    ( a_truth(Statement)
    | ~ a_truth(says(Liar,Statement))
    | a_truth(liar(Liar)) ) ).

%--------------------------------------------------------------------------

```

### ./PUZ003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : PUZ003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Puzzles (Truthtellers and Liars)
% Axioms   : Truthtellers and Liars axioms for three types of people
% Version  : [ANL] axioms.
% English  : Axioms for three types of people; truthtellers, liars and
%            normal people.

% Refs     : [Smu78] Smullyan (1978), What is the name of this book?-The ri
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   0 unt;   3 nHn;   7 RR)
%            Number of literals    :   23 (   0 equ;  14 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :   12 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%-----The next 4 clauses says that a person is one thing
cnf(person_is_one_type,axiom,
    ( a_truth(truthteller(X))
    | a_truth(liar(X))
    | a_truth(normal(X)) ) ).

cnf(not_truthteller_and_normal,axiom,
    ( ~ a_truth(truthteller(X))
    | ~ a_truth(normal(X)) ) ).

cnf(not_truthteller_and_liar,axiom,
    ( ~ a_truth(truthteller(X))
    | ~ a_truth(liar(X)) ) ).

cnf(not_liar_and_normal,axiom,
    ( ~ a_truth(liar(X))
    | ~ a_truth(normal(X)) ) ).

cnf(truthtellers_tell_truth,axiom,
    ( ~ a_truth(truthteller(X))
    | ~ a_truth(says(X,Y))
    | a_truth(Y) ) ).

cnf(liars_lie,axiom,
    ( ~ a_truth(liar(X))
    | ~ a_truth(says(X,Y))
    | ~ a_truth(Y) ) ).

cnf(truthtellers_and_normal_tell_truth,axiom,
    ( ~ a_truth(X)
    | ~ a_truth(says(Y,X))
    | a_truth(truthteller(Y))
    | a_truth(normal(Y)) ) ).

cnf(liars_and_normal_lie,axiom,
    ( a_truth(X)
    | ~ a_truth(says(Y,X))
    | a_truth(liar(Y))
    | a_truth(normal(Y)) ) ).

%--------------------------------------------------------------------------

```

### ./PUZ004-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : PUZ004-0 : TPTP v8.2.0. Released v2.4.0.
% Domain   : Puzzles (Quo Vadis)
% Axioms   : Quo vadis axioms
% Version  :
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   41 (   0 unt;   0 nHn;  41 RR)
%            Number of literals    :   82 (   0 equ;  41 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 12-12 aty)
%            Number of functors    :   13 (  13 usr;   0 con; 1-2 aty)
%            Number of variables   :  480 (   0 sgn)
% SPC      : 

% Comments : Contributed by Christian Suttner
%------------------------------------------------------------------------------
cnf(s1_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,s(Y)),S2,S3,S4,e1(X,Y),E2) ) ).

cnf(s1_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,s(Y)),S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(X,s(Y)),E2) ) ).

cnf(s1_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(s(X),Y),S2,S3,S4,e1(X,Y),E2) ) ).

cnf(s1_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(s(X),Y),S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(s(X),Y),E2) ) ).

cnf(s2_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,s(Y)),S3,S4,e1(X,Y),E2) ) ).

cnf(s2_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,s(Y)),S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(X,s(Y)),E2) ) ).

cnf(s2_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(s(X),Y),S3,S4,e1(X,Y),E2) ) ).

cnf(s2_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(s(X),Y),S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(s(X),Y),E2) ) ).

cnf(s3_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,s(Y)),S4,e1(X,Y),E2) ) ).

cnf(s3_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,s(Y)),S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(X,s(Y)),E2) ) ).

cnf(s3_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(s(X),Y),S4,e1(X,Y),E2) ) ).

cnf(s3_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(s(X),Y),S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(s(X),Y),E2) ) ).

cnf(s4_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,s(Y)),e1(X,Y),E2) ) ).

cnf(s4_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,s(Y)),e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(X,s(Y)),E2) ) ).

cnf(s4_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(s(X),Y),e1(X,Y),E2) ) ).

cnf(s4_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(s(X),Y),e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(s(X),Y),E2) ) ).

cnf(v1_right,axiom,
    ( ~ state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,v1(X,s(Y)),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) ) ).

cnf(v1_left,axiom,
    ( ~ state(B,v1(X,s(Y)),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) ) ).

cnf(v1_down,axiom,
    ( ~ state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,v1(s(X),Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2) ) ).

cnf(v1_up,axiom,
    ( ~ state(B,v1(s(X),Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) ) ).

cnf(v2_right,axiom,
    ( ~ state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,v2(X,s(Y)),V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) ) ).

cnf(v2_left,axiom,
    ( ~ state(B,V1,v2(X,s(Y)),V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) ) ).

cnf(v2_down,axiom,
    ( ~ state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,v2(s(X),Y),V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2) ) ).

cnf(v2_up,axiom,
    ( ~ state(B,V1,v2(s(X),Y),V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) ) ).

cnf(v3_right,axiom,
    ( ~ state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,V2,v3(X,s(Y)),V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) ) ).

cnf(v3_left,axiom,
    ( ~ state(B,V1,V2,v3(X,s(Y)),V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) ) ).

cnf(v3_down,axiom,
    ( ~ state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,V2,v3(s(X),Y),V4,H,S1,S2,S3,S4,e1(X,Y),E2) ) ).

cnf(v3_up,axiom,
    ( ~ state(B,V1,V2,v3(s(X),Y),V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) ) ).

cnf(v4_right,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,V2,V3,v4(X,s(Y)),H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) ) ).

cnf(v4_left,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,s(Y)),H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) ) ).

cnf(v4_down,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,V2,V3,v4(s(X),Y),H,S1,S2,S3,S4,e1(X,Y),E2) ) ).

cnf(v4_up,axiom,
    ( ~ state(B,V1,V2,V3,v4(s(X),Y),H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) ) ).

cnf(h_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(X,s(s(Y))),E2)
    | state(B,V1,V2,V3,V4,h(X,s(Y)),S1,S2,S3,S4,e1(X,Y),E2) ) ).

cnf(h_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,s(Y)),S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(X,s(s(Y))),E2) ) ).

cnf(h_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(s(X),Y),e2(s(X),s(Y)))
    | state(B,V1,V2,V3,V4,h(s(X),Y),S1,S2,S3,S4,e1(X,Y),e2(X,s(Y))) ) ).

cnf(h_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(s(X),Y),S1,S2,S3,S4,e1(X,Y),e2(X,s(Y)))
    | state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(s(X),Y),e2(s(X),s(Y))) ) ).

cnf(b_right,axiom,
    ( ~ state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(s(Y))),e2(s(X),s(s(Y))))
    | state(bb(X,s(Y)),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) ) ).

cnf(b_left,axiom,
    ( ~ state(bb(X,s(Y)),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(s(Y))),e2(s(X),s(s(Y)))) ) ).

cnf(b_down,axiom,
    ( ~ state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),e2(s(s(X)),s(Y)))
    | state(bb(s(X),Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(X,s(Y))) ) ).

cnf(b_up,axiom,
    ( ~ state(bb(s(X),Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(X,s(Y)))
    | state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),e2(s(s(X)),s(Y))) ) ).

cnf(swap_blanks,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(Q,W))
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,S4,e1(Q,W),e2(X,Y)) ) ).

%------------------------------------------------------------------------------

```

### ./PUZ005+0.ax

Very long 4664

### ./PUZ005-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : PUZ005-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Puzzles (Sudoku)
% Axioms   : Sudoku axioms
% Version  : [Bau06] axioms : Especial.
% English  :

% Refs     : [Bau06] Baumgartner (2006), Email to G. Sutcliffe
% Source   : [Bau06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   79 (  54 unt;   4 nHn;  79 RR)
%            Number of literals    :  161 (  39 equ; 104 neg)
%            Maximal clause size   :   11 (   2 avg)
%            Maximal term depth    :   10 (   3 avg)
%            Number of predicates  :    4 (   3 usr;   0 prp; 1-3 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :   75 (   0 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Regarding equality, (un)equality is syntactic (un)equality
%----The domain is the numbers from n1 to n9.
cnf(dom_1,axiom,
    dom(s(n0)) ).

cnf(dom_2,axiom,
    dom(s(s(n0))) ).

cnf(dom_3,axiom,
    dom(s(s(s(n0)))) ).

cnf(dom_4,axiom,
    dom(s(s(s(s(n0))))) ).

cnf(dom_5,axiom,
    dom(s(s(s(s(s(n0)))))) ).

cnf(dom_6,axiom,
    dom(s(s(s(s(s(s(n0))))))) ).

cnf(dom_7,axiom,
    dom(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_8,axiom,
    dom(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_9,axiom,
    dom(s(s(s(s(s(s(s(s(s(n0)))))))))) ).

%----The domain elements are pairwise different;
%----This is the negative part of equality.
cnf(dom_1_not_2,axiom,
    s(n0) != s(s(n0)) ).

cnf(dom_1_not_3,axiom,
    s(n0) != s(s(s(n0))) ).

cnf(dom_1_not_4,axiom,
    s(n0) != s(s(s(s(n0)))) ).

cnf(dom_1_not_5,axiom,
    s(n0) != s(s(s(s(s(n0))))) ).

cnf(dom_1_not_6,axiom,
    s(n0) != s(s(s(s(s(s(n0)))))) ).

cnf(dom_1_not_7,axiom,
    s(n0) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_1_not_8,axiom,
    s(n0) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_1_not_9,axiom,
    s(n0) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_2_not_3,axiom,
    s(s(n0)) != s(s(s(n0))) ).

cnf(dom_2_not_4,axiom,
    s(s(n0)) != s(s(s(s(n0)))) ).

cnf(dom_2_not_5,axiom,
    s(s(n0)) != s(s(s(s(s(n0))))) ).

cnf(dom_2_not_6,axiom,
    s(s(n0)) != s(s(s(s(s(s(n0)))))) ).

cnf(dom_2_not_7,axiom,
    s(s(n0)) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_2_not_8,axiom,
    s(s(n0)) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_2_not_9,axiom,
    s(s(n0)) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_3_not_4,axiom,
    s(s(s(n0))) != s(s(s(s(n0)))) ).

cnf(dom_3_not_5,axiom,
    s(s(s(n0))) != s(s(s(s(s(n0))))) ).

cnf(dom_3_not_6,axiom,
    s(s(s(n0))) != s(s(s(s(s(s(n0)))))) ).

cnf(dom_3_not_7,axiom,
    s(s(s(n0))) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_3_not_8,axiom,
    s(s(s(n0))) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_3_not_9,axiom,
    s(s(s(n0))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_4_not_5,axiom,
    s(s(s(s(n0)))) != s(s(s(s(s(n0))))) ).

cnf(dom_4_not_6,axiom,
    s(s(s(s(n0)))) != s(s(s(s(s(s(n0)))))) ).

cnf(dom_4_not_7,axiom,
    s(s(s(s(n0)))) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_4_not_8,axiom,
    s(s(s(s(n0)))) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_4_not_9,axiom,
    s(s(s(s(n0)))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_5_not_6,axiom,
    s(s(s(s(s(n0))))) != s(s(s(s(s(s(n0)))))) ).

cnf(dom_5_not_7,axiom,
    s(s(s(s(s(n0))))) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_5_not_8,axiom,
    s(s(s(s(s(n0))))) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_5_not_9,axiom,
    s(s(s(s(s(n0))))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_6_not_7,axiom,
    s(s(s(s(s(s(n0)))))) != s(s(s(s(s(s(s(n0))))))) ).

cnf(dom_6_not_8,axiom,
    s(s(s(s(s(s(n0)))))) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_6_not_9,axiom,
    s(s(s(s(s(s(n0)))))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_7_not_8,axiom,
    s(s(s(s(s(s(s(n0))))))) != s(s(s(s(s(s(s(s(n0)))))))) ).

cnf(dom_7_not_9,axiom,
    s(s(s(s(s(s(s(n0))))))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

cnf(dom_8_not_9,axiom,
    s(s(s(s(s(s(s(s(n0)))))))) != s(s(s(s(s(s(s(s(s(n0))))))))) ).

%----Generator:
%----At least one number in each field
%----el(I,J,X) means on row I, column J is the natural number X
cnf(number_in_each_position,axiom,
    ( ~ dom(I)
    | ~ dom(J)
    | el(I,J,s(n0))
    | el(I,J,s(s(n0)))
    | el(I,J,s(s(s(n0))))
    | el(I,J,s(s(s(s(n0)))))
    | el(I,J,s(s(s(s(s(n0))))))
    | el(I,J,s(s(s(s(s(s(n0)))))))
    | el(I,J,s(s(s(s(s(s(s(n0))))))))
    | el(I,J,s(s(s(s(s(s(s(s(n0)))))))))
    | el(I,J,s(s(s(s(s(s(s(s(s(n0)))))))))) ) ).

%----Restriction:
%----No two same numbers on a field (dual of previous)
%----This is in fact redundant in combination of the previous generator and
%----already one of the following constraints
cnf(only_one_number_in_each_position,axiom,
    ( ~ el(I,J,X)
    | ~ el(I,J,X1)
    | X = X1 ) ).

%----Restriction:
%----No number occurs twice in a row:
%----(J = J1) :- el(I,J,X), el(I,J1,X1), (X = X1).
%----slightly simpler:
cnf(no_duplicates_in_a_row,axiom,
    ( ~ el(I,J,X)
    | ~ el(I,J1,X)
    | J = J1 ) ).

%----Restriction:
%----No number occurs twice in a column:
cnf(no_duplicates_in_a_column,axiom,
    ( ~ el(I,J,X)
    | ~ el(I1,J,X)
    | I = I1 ) ).

%----where different(I,J,I1,J1) means that the field elements at
%----(I,J) and at (I1,J1) are different
%---- different(I,J,I1,J1) ->
%       ( el(I,J,X) & el(I1,J1,X1) -> -(X = X1)).
%----Now, the n3x3 subfields.
cnf(subfield_1_1,hypothesis,
    subfield(s(n0),s(n0)) ).

cnf(subfield_1_4,hypothesis,
    subfield(s(n0),s(s(s(s(n0))))) ).

cnf(subfield_1_7,hypothesis,
    subfield(s(n0),s(s(s(s(s(s(s(n0)))))))) ).

cnf(subfield_4_1,hypothesis,
    subfield(s(s(s(s(n0)))),s(n0)) ).

cnf(subfield_4_4,hypothesis,
    subfield(s(s(s(s(n0)))),s(s(s(s(n0))))) ).

cnf(subfield_4_7,hypothesis,
    subfield(s(s(s(s(n0)))),s(s(s(s(s(s(s(n0)))))))) ).

cnf(subfield_7_1,hypothesis,
    subfield(s(s(s(s(s(s(s(n0))))))),s(n0)) ).

cnf(subfield_7_4,hypothesis,
    subfield(s(s(s(s(s(s(s(n0))))))),s(s(s(s(n0))))) ).

cnf(subfield_7_7,hypothesis,
    subfield(s(s(s(s(s(s(s(n0))))))),s(s(s(s(s(s(s(n0)))))))) ).

%----Each subfield contains no number twice:
%----Note: It is sufficient to specify only along the diagonals,
%----as along the row and columns the general row and column restrictions
%----above subsume the corresponding ones for the subfields.
%----Notice we do a little bit of integer arithmetic (+1 and +2) to talk
%----about the fields in a given subfield.
%----Perhaps more readable formulation of the axioms is like
%----subfield(I,J) ->
%---- ( el(I,J,X) & el(s(I),s(J),X1) -> -(X = X1)).
%----which translates to
cnf(subfield_diagonal_1,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,J,X)
    | ~ el(s(I),s(J),X) ) ).

cnf(subfield_diagonal_2,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,J,X)
    | ~ el(s(I),s(s(J)),X) ) ).

cnf(subfield_diagonal_3,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,J,X)
    | ~ el(s(s(I)),s(J),X) ) ).

cnf(subfield_diagonal_4,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,J,X)
    | ~ el(s(s(I)),s(s(J)),X) ) ).

cnf(subfield_diagonal_5,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(J),X)
    | ~ el(s(I),J,X) ) ).

cnf(subfield_diagonal_6,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(J),X)
    | ~ el(s(I),s(s(J)),X) ) ).

cnf(subfield_diagonal_7,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(J),X)
    | ~ el(s(s(I)),J,X) ) ).

cnf(subfield_diagonal_8,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(J),X)
    | ~ el(s(s(I)),s(s(J)),X) ) ).

cnf(subfield_diagonal_9,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(s(J)),X)
    | ~ el(s(I),J,X) ) ).

cnf(subfield_diagonal_10,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(s(J)),X)
    | ~ el(s(I),s(J),X) ) ).

cnf(subfield_diagonal_11,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(s(J)),X)
    | ~ el(s(s(I)),J,X) ) ).

cnf(subfield_diagonal_12,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(I,s(s(J)),X)
    | ~ el(s(s(I)),s(J),X) ) ).

cnf(subfield_diagonal_13,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),J,X)
    | ~ el(s(s(I)),s(J),X) ) ).

cnf(subfield_diagonal_14,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),J,X)
    | ~ el(s(s(I)),s(s(J)),X) ) ).

cnf(subfield_diagonal_15,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),s(J),X)
    | ~ el(s(s(I)),J,X) ) ).

cnf(subfield_diagonal_16,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),s(J),X)
    | ~ el(s(s(I)),s(s(J)),X) ) ).

cnf(subfield_diagonal_17,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),s(s(J)),X)
    | ~ el(s(s(I)),J,X) ) ).

cnf(subfield_diagonal_18,hypothesis,
    ( ~ subfield(I,J)
    | ~ el(s(I),s(s(J)),X)
    | ~ el(s(s(I)),s(J),X) ) ).

%----Some additional constraints. They are redundant but help
%----to solve the Sudoku in a deterministic way quite often.
%----I think the underlying heuristics used by people is called
%----'crosshatching'.
%----In every subfield, every value must be put somewhere
cnf(value_somewhere_in_subfield,hypothesis,
    ( ~ subfield(I,J)
    | ~ dom(X)
    | el(I,J,X)
    | el(I,s(J),X)
    | el(I,s(s(J)),X)
    | el(s(I),J,X)
    | el(s(I),s(J),X)
    | el(s(I),s(s(J)),X)
    | el(s(s(I)),J,X)
    | el(s(s(I)),s(J),X)
    | el(s(s(I)),s(s(J)),X) ) ).

%----In every row, every value must be put somewhere
cnf(value_somewhere_in_row,hypothesis,
    ( ~ dom(I)
    | ~ dom(X)
    | el(I,s(n0),X)
    | el(I,s(s(n0)),X)
    | el(I,s(s(s(n0))),X)
    | el(I,s(s(s(s(n0)))),X)
    | el(I,s(s(s(s(s(n0))))),X)
    | el(I,s(s(s(s(s(s(n0)))))),X)
    | el(I,s(s(s(s(s(s(s(n0))))))),X)
    | el(I,s(s(s(s(s(s(s(s(n0)))))))),X)
    | el(I,s(s(s(s(s(s(s(s(s(n0))))))))),X) ) ).

%----In every column, every value must be put somewhere
cnf(value_somewhere_in_column,hypothesis,
    ( ~ dom(J)
    | ~ dom(X)
    | el(s(n0),J,X)
    | el(s(s(n0)),J,X)
    | el(s(s(s(n0))),J,X)
    | el(s(s(s(s(n0)))),J,X)
    | el(s(s(s(s(s(n0))))),J,X)
    | el(s(s(s(s(s(s(n0)))))),J,X)
    | el(s(s(s(s(s(s(s(n0))))))),J,X)
    | el(s(s(s(s(s(s(s(s(n0)))))))),J,X)
    | el(s(s(s(s(s(s(s(s(s(n0))))))))),J,X) ) ).

%------------------------------------------------------------------------------

```

### ./PUZ006+0.ax

Very long 44452

## Quantales

### ./QUA001^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : QUA001^0 : TPTP v8.2.0. Released v4.1.0.
% Domain   : Quantales
% Axioms   : Quantales
% Version  : [Hoe09] axioms.
% English  :

% Refs     : [Con71] Conway (1971), Regular Algebra and Finite Machines
%          : [Hoe09] Hoefner (2009), Email to Geoff Sutcliffe
% Source   : [Hoe09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   26 (  13 unt;  12 typ;   7 def)
%            Number of atoms       :   33 (  17 equ;   0 cnn)
%            Maximal formula atoms :    2 (   1 avg)
%            Number of connectives :   43 (   0   ~;   1   |;   4   &;  37   @)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   2 avg;  37 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   43 (  43   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   14 (  12 usr;   3 con; 0-3 aty)
%            Number of variables   :   27 (  15   ^   8   !;   4   ?;  27   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Usual Definition of Set Theory
thf(emptyset_type,type,
    emptyset: $i > $o ).

thf(emptyset_def,definition,
    ( emptyset
    = ( ^ [X: $i] : $false ) ) ).

thf(union_type,type,
    union: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(union_def,definition,
    ( union
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

thf(singleton_type,type,
    singleton: $i > $i > $o ).

thf(singleton_def,definition,
    ( singleton
    = ( ^ [X: $i,U: $i] : ( U = X ) ) ) ).

%----Supremum Definition
thf(zero_type,type,
    zero: $i ).

thf(sup_type,type,
    sup: ( $i > $o ) > $i ).

thf(sup_es,axiom,
    ( ( sup @ emptyset )
    = zero ) ).

thf(sup_singleset,axiom,
    ! [X: $i] :
      ( ( sup @ ( singleton @ X ) )
      = X ) ).

thf(supset_type,type,
    supset: ( ( $i > $o ) > $o ) > $i > $o ).

thf(supset,definition,
    ( supset
    = ( ^ [F: ( $i > $o ) > $o,X: $i] :
        ? [Y: $i > $o] :
          ( ( F @ Y )
          & ( ( sup @ Y )
            = X ) ) ) ) ).

thf(unionset_type,type,
    unionset: ( ( $i > $o ) > $o ) > $i > $o ).

thf(unionset,definition,
    ( unionset
    = ( ^ [F: ( $i > $o ) > $o,X: $i] :
        ? [Y: $i > $o] :
          ( ( F @ Y )
          & ( Y @ X ) ) ) ) ).

thf(sup_set,axiom,
    ! [X: ( $i > $o ) > $o] :
      ( ( sup @ ( supset @ X ) )
      = ( sup @ ( unionset @ X ) ) ) ).

%----Definition of binary sums and lattice order
thf(addition_type,type,
    addition: $i > $i > $i ).

thf(addition_def,definition,
    ( addition
    = ( ^ [X: $i,Y: $i] : ( sup @ ( union @ ( singleton @ X ) @ ( singleton @ Y ) ) ) ) ) ).

thf(order_type,type,
    leq: $i > $i > $o ).

thf(order_def,axiom,
    ! [X1: $i,X2: $i] :
      ( ( leq @ X1 @ X2 )
    <=> ( ( addition @ X1 @ X2 )
        = X2 ) ) ).

%----Definition of multiplication
thf(multiplication_type,type,
    multiplication: $i > $i > $i ).

thf(crossmult_type,type,
    crossmult: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(crossmult_def,definition,
    ( crossmult
    = ( ^ [X: $i > $o,Y: $i > $o,A: $i] :
        ? [X1: $i,Y1: $i] :
          ( ( X @ X1 )
          & ( Y @ Y1 )
          & ( A
            = ( multiplication @ X1 @ Y1 ) ) ) ) ) ).

thf(multiplication_def,axiom,
    ! [X: $i > $o,Y: $i > $o] :
      ( ( multiplication @ ( sup @ X ) @ ( sup @ Y ) )
      = ( sup @ ( crossmult @ X @ Y ) ) ) ).

thf(one_type,type,
    one: $i ).

thf(multiplication_neutral_right,axiom,
    ! [X: $i] :
      ( ( multiplication @ X @ one )
      = X ) ).

thf(multiplication_neutral_left,axiom,
    ! [X: $i] :
      ( ( multiplication @ one @ X )
      = X ) ).

%------------------------------------------------------------------------------

```

### ./QUA001^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : QUA001^1 : TPTP v8.2.0. Released v4.1.0.
% Domain   : Quantales
% Axioms   : Tests for Quantales (Boolean sub-algebra below 1)
% Version  : [Hoe09] axioms.
% English  :

% Refs     : [Con71] Conway (1971), Regular Algebra and Finite Machines
%          : [Koz97] Kozen (1997), Kleene Algebra with Tests
%          : [Hoe09] Hoefner (2009), Email to Geoff Sutcliffe
% Source   : [Hoe09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   0 unt;   1 typ;   0 def)
%            Number of atoms       :   10 (   3 equ;   0 cnn)
%            Maximal formula atoms :    4 (   5 avg)
%            Number of connectives :   10 (   0   ~;   0   |;   2   &;   7   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   6 avg;   7 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    6 (   5 usr;   4 con; 0-2 aty)
%            Number of variables   :    2 (   0   ^   1   !;   1   ?;   2   :)
% SPC      : 

% Comments : Requires QUA001^0.ax
%------------------------------------------------------------------------------
thf(tests,type,
    test: $i > $o ).

thf(test_definition,axiom,
    ! [X: $i] :
      ( ( test @ X )
     => ? [Y: $i] :
          ( ( ( addition @ X @ Y )
            = one )
          & ( ( multiplication @ X @ Y )
            = zero )
          & ( ( multiplication @ Y @ X )
            = zero ) ) ) ).

%------------------------------------------------------------------------------

```

## Relation Algebra

### ./REL001+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : REL001+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Relation Algebra
% Axioms   : Relation Algebra
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Mad95] Maddux, R. (1995), Relation-algebraic semantics
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   13 (  13 unt;   0 def)
%            Number of atoms       :   13 (  13 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   3 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-2 aty)
%            Number of variables   :   25 (  25   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Definition of Boolean algebra a la Maddux
fof(maddux1_join_commutativity,axiom,
    ! [X0,X1] : join(X0,X1) = join(X1,X0) ).

fof(maddux2_join_associativity,axiom,
    ! [X0,X1,X2] : join(X0,join(X1,X2)) = join(join(X0,X1),X2) ).

fof(maddux3_a_kind_of_de_Morgan,axiom,
    ! [X0,X1] : X0 = join(complement(join(complement(X0),complement(X1))),complement(join(complement(X0),X1))) ).

fof(maddux4_definiton_of_meet,axiom,
    ! [X0,X1] : meet(X0,X1) = complement(join(complement(X0),complement(X1))) ).

%----Definition of Sequential Composition
fof(composition_associativity,axiom,
    ! [X0,X1,X2] : composition(X0,composition(X1,X2)) = composition(composition(X0,X1),X2) ).

fof(composition_identity,axiom,
    ! [X0] : composition(X0,one) = X0 ).

fof(composition_distributivity,axiom,
    ! [X0,X1,X2] : composition(join(X0,X1),X2) = join(composition(X0,X2),composition(X1,X2)) ).

%----Definition of Converse
fof(converse_idempotence,axiom,
    ! [X0] : converse(converse(X0)) = X0 ).

fof(converse_additivity,axiom,
    ! [X0,X1] : converse(join(X0,X1)) = join(converse(X0),converse(X1)) ).

fof(converse_multiplicativity,axiom,
    ! [X0,X1] : converse(composition(X0,X1)) = composition(converse(X1),converse(X0)) ).

fof(converse_cancellativity,axiom,
    ! [X0,X1] : join(composition(converse(X0),complement(composition(X0,X1))),complement(X1)) = complement(X1) ).

%---Definition of Identities (greatest and smallest element)
fof(def_top,axiom,
    ! [X0] : top = join(X0,complement(X0)) ).

fof(def_zero,axiom,
    ! [X0] : zero = meet(X0,complement(X0)) ).

%------------------------------------------------------------------------------

```

### ./REL001+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : REL001+1 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Relation Algebra
% Axioms   : Dedkind and two modular laws
% Version  : [Hoe08] axioms.
% English  :

% Refs     : [Mad95] Maddux, R. (1995), Relation-algebraic semantics
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   3 unt;   0 def)
%            Number of atoms       :    3 (   3 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   4 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :    9 (   9   !;   0   ?)
% SPC      : 

% Comments : Requires REL001+0.ax
%------------------------------------------------------------------------------
%---Dedekind law
fof(dedekind_law,axiom,
    ! [X0,X1,X2] : join(meet(composition(X0,X1),X2),composition(meet(X0,composition(X2,converse(X1))),meet(X1,composition(converse(X0),X2)))) = composition(meet(X0,composition(X2,converse(X1))),meet(X1,composition(converse(X0),X2))) ).

%---modular laws
fof(modular_law_1,axiom,
    ! [X0,X1,X2] : join(meet(composition(X0,X1),X2),meet(composition(X0,meet(X1,composition(converse(X0),X2))),X2)) = meet(composition(X0,meet(X1,composition(converse(X0),X2))),X2) ).

fof(modular_law_2,axiom,
    ! [X0,X1,X2] : join(meet(composition(X0,X1),X2),meet(composition(meet(X0,composition(X2,converse(X1))),X1),X2)) = meet(composition(meet(X0,composition(X2,converse(X1))),X1),X2) ).

%------------------------------------------------------------------------------

```

### ./REL001-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : REL001-0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Relation Algebra
% Axioms   : Relation algebra
% Version  : [Mad95] (equational) axioms.
% English  :

% Refs     : [Mad95] Maddux (1995), Relation-Algebraic Semantics
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Rating   : ? v3.6.0
% Syntax   : Number of clauses     :   13 (  13 unt;   0 nHn;   0 RR)
%            Number of literals    :   13 (  13 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-2 aty)
%            Number of variables   :   25 (   0 sgn)
% SPC      : 

% Comments : tptp2X -f tptp:short -t cnf:otter REL001+0.ax
%------------------------------------------------------------------------------
cnf(maddux1_join_commutativity_1,axiom,
    join(A,B) = join(B,A) ).

cnf(maddux2_join_associativity_2,axiom,
    join(A,join(B,C)) = join(join(A,B),C) ).

cnf(maddux3_a_kind_of_de_Morgan_3,axiom,
    A = join(complement(join(complement(A),complement(B))),complement(join(complement(A),B))) ).

cnf(maddux4_definiton_of_meet_4,axiom,
    meet(A,B) = complement(join(complement(A),complement(B))) ).

cnf(composition_associativity_5,axiom,
    composition(A,composition(B,C)) = composition(composition(A,B),C) ).

cnf(composition_identity_6,axiom,
    composition(A,one) = A ).

cnf(composition_distributivity_7,axiom,
    composition(join(A,B),C) = join(composition(A,C),composition(B,C)) ).

cnf(converse_idempotence_8,axiom,
    converse(converse(A)) = A ).

cnf(converse_additivity_9,axiom,
    converse(join(A,B)) = join(converse(A),converse(B)) ).

cnf(converse_multiplicativity_10,axiom,
    converse(composition(A,B)) = composition(converse(B),converse(A)) ).

cnf(converse_cancellativity_11,axiom,
    join(composition(converse(A),complement(composition(A,B))),complement(B)) = complement(B) ).

cnf(def_top_12,axiom,
    top = join(A,complement(A)) ).

cnf(def_zero_13,axiom,
    zero = meet(A,complement(A)) ).

%------------------------------------------------------------------------------

```

### ./REL001-1.ax

```vampire
%------------------------------------------------------------------------------
% File     : REL001-1 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Relation Algebra
% Axioms   : Dedkind and two modular laws
% Version  : [Mad95] (equational) axioms : Augmented.
% English  :

% Refs     : [Mad95] Maddux (1995), Relation-Algebraic Semantics
%          : [Hoe08] Hoefner (2008), Email to G. Sutcliffe
% Source   : [Hoe08]
% Names    :

% Status   : Satisfiable
% Rating   : ? v3.6.0
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   0 RR)
%            Number of literals    :    3 (   3 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   0 con; 1-2 aty)
%            Number of variables   :    9 (   0 sgn)
% SPC      : 

% Comments : tptp2X -f tptp:short -t cnf:otter REL001+1.ax
%------------------------------------------------------------------------------
cnf(dedekind_law_14,axiom,
    join(meet(composition(A,B),C),composition(meet(A,composition(C,converse(B))),meet(B,composition(converse(A),C)))) = composition(meet(A,composition(C,converse(B))),meet(B,composition(converse(A),C))) ).

cnf(modular_law_1_15,axiom,
    join(meet(composition(A,B),C),meet(composition(A,meet(B,composition(converse(A),C))),C)) = meet(composition(A,meet(B,composition(converse(A),C))),C) ).

cnf(modular_law_2_16,axiom,
    join(meet(composition(A,B),C),meet(composition(meet(A,composition(C,converse(B))),B),C)) = meet(composition(meet(A,composition(C,converse(B))),B),C) ).

%------------------------------------------------------------------------------

```

## Ring Theory

### ./RNG001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : RNG001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Ring Theory
% Axioms   : Ring theory axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   17 (   6 unt;   0 nHn;  11 RR)
%            Number of literals    :   50 (   2 equ;  33 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   71 (   0 sgn)
% SPC      : 

% Comments : These axioms are used in [Wos88] p.201.
%--------------------------------------------------------------------------
cnf(additive_identity1,axiom,
    sum(additive_identity,X,X) ).

cnf(additive_identity2,axiom,
    sum(X,additive_identity,X) ).

cnf(closure_of_multiplication,axiom,
    product(X,Y,multiply(X,Y)) ).

cnf(closure_of_addition,axiom,
    sum(X,Y,add(X,Y)) ).

cnf(left_inverse,axiom,
    sum(additive_inverse(X),X,additive_identity) ).

cnf(right_inverse,axiom,
    sum(X,additive_inverse(X),additive_identity) ).

cnf(associativity_of_addition1,axiom,
    ( ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(U,Z,W)
    | sum(X,V,W) ) ).

cnf(associativity_of_addition2,axiom,
    ( ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(X,V,W)
    | sum(U,Z,W) ) ).

cnf(commutativity_of_addition,axiom,
    ( ~ sum(X,Y,Z)
    | sum(Y,X,Z) ) ).

cnf(associativity_of_multiplication1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity_of_multiplication2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

cnf(distributivity1,axiom,
    ( ~ product(X,Y,V1)
    | ~ product(X,Z,V2)
    | ~ sum(Y,Z,V3)
    | ~ product(X,V3,V4)
    | sum(V1,V2,V4) ) ).

cnf(distributivity2,axiom,
    ( ~ product(X,Y,V1)
    | ~ product(X,Z,V2)
    | ~ sum(Y,Z,V3)
    | ~ sum(V1,V2,V4)
    | product(X,V3,V4) ) ).

cnf(distributivity3,axiom,
    ( ~ product(Y,X,V1)
    | ~ product(Z,X,V2)
    | ~ sum(Y,Z,V3)
    | ~ product(V3,X,V4)
    | sum(V1,V2,V4) ) ).

cnf(distributivity4,axiom,
    ( ~ product(Y,X,V1)
    | ~ product(Z,X,V2)
    | ~ sum(Y,Z,V3)
    | ~ sum(V1,V2,V4)
    | product(V3,X,V4) ) ).

%-----Equality axioms for operators
cnf(addition_is_well_defined,axiom,
    ( ~ sum(X,Y,U)
    | ~ sum(X,Y,V)
    | U = V ) ).

cnf(multiplication_is_well_defined,axiom,
    ( ~ product(X,Y,U)
    | ~ product(X,Y,V)
    | U = V ) ).

%--------------------------------------------------------------------------

```

### ./RNG002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : RNG002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Ring Theory
% Axioms   : Ring theory (equality) axioms
% Version  : [PS81] (equality) axioms :
%            Reduced & Augmented > Complete.
% English  :

% Refs     : [PS81]  Peterson & Stickel (1981), Complete Sets of Reductions
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   14 (  14 unt;   0 nHn;   1 RR)
%            Number of literals    :   14 (  14 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   25 (   2 sgn)
% SPC      : 

% Comments : Not sure if these are complete. I don't know if the reductions
%            given in [PS81] are suitable for ATP.
%--------------------------------------------------------------------------
%----Existence of left identity for addition
cnf(left_identity,axiom,
    add(additive_identity,X) = X ).

%----Existence of left additive additive_inverse
cnf(left_additive_inverse,axiom,
    add(additive_inverse(X),X) = additive_identity ).

%----Distributive property of product over sum
cnf(distribute1,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(distribute2,axiom,
    multiply(add(X,Y),Z) = add(multiply(X,Z),multiply(Y,Z)) ).

%----Inverse of identity is identity, stupid
cnf(additive_inverse_identity,axiom,
    additive_inverse(additive_identity) = additive_identity ).

%----Inverse of additive_inverse of X is X
cnf(additive_inverse_additive_inverse,axiom,
    additive_inverse(additive_inverse(X)) = X ).

%----Behavior of 0 and the multiplication operation
cnf(multiply_additive_id1,axiom,
    multiply(X,additive_identity) = additive_identity ).

cnf(multiply_additive_id2,axiom,
    multiply(additive_identity,X) = additive_identity ).

%----Inverse of (x + y) is additive_inverse(x) + additive_inverse(y)
cnf(distribute_additive_inverse,axiom,
    additive_inverse(add(X,Y)) = add(additive_inverse(X),additive_inverse(Y)) ).

%----x * additive_inverse(y) = additive_inverse (x * y)
cnf(multiply_additive_inverse1,axiom,
    multiply(X,additive_inverse(Y)) = additive_inverse(multiply(X,Y)) ).

cnf(multiply_additive_inverse2,axiom,
    multiply(additive_inverse(X),Y) = additive_inverse(multiply(X,Y)) ).

%----Associativity of addition
cnf(associative_addition,axiom,
    add(add(X,Y),Z) = add(X,add(Y,Z)) ).

%----Commutativity of addition
cnf(commutative_addition,axiom,
    add(X,Y) = add(Y,X) ).

%----Associativity of product
cnf(associative_multiplication,axiom,
    multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).

%--------------------------------------------------------------------------

```

### ./RNG003-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : RNG003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Ring Theory (Alternative)
% Axioms   : Alternative ring theory (equality) axioms
% Version  : [Ste87] (equality) axioms.
% English  :

% Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin
% Source   : [Ste87]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   15 (  15 unt;   0 nHn;   0 RR)
%            Number of literals    :   15 (  15 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   1 con; 0-3 aty)
%            Number of variables   :   27 (   2 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----There exists an additive identity element
cnf(left_additive_identity,axiom,
    add(additive_identity,X) = X ).

cnf(right_additive_identity,axiom,
    add(X,additive_identity) = X ).

%----Multiplicative zero
cnf(left_multiplicative_zero,axiom,
    multiply(additive_identity,X) = additive_identity ).

cnf(right_multiplicative_zero,axiom,
    multiply(X,additive_identity) = additive_identity ).

%----Existence of left additive additive_inverse
cnf(left_additive_inverse,axiom,
    add(additive_inverse(X),X) = additive_identity ).

cnf(right_additive_inverse,axiom,
    add(X,additive_inverse(X)) = additive_identity ).

%----Inverse of additive_inverse of X is X
cnf(additive_inverse_additive_inverse,axiom,
    additive_inverse(additive_inverse(X)) = X ).

%----Distributive property of product over sum
cnf(distribute1,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(distribute2,axiom,
    multiply(add(X,Y),Z) = add(multiply(X,Z),multiply(Y,Z)) ).

%----Commutativity for addition
cnf(commutativity_for_addition,axiom,
    add(X,Y) = add(Y,X) ).

%----Associativity for addition
cnf(associativity_for_addition,axiom,
    add(X,add(Y,Z)) = add(add(X,Y),Z) ).

%----Right alternative law
cnf(right_alternative,axiom,
    multiply(multiply(X,Y),Y) = multiply(X,multiply(Y,Y)) ).

%----Left alternative law
cnf(left_alternative,axiom,
    multiply(multiply(X,X),Y) = multiply(X,multiply(X,Y)) ).

%----Associator
cnf(associator,axiom,
    associator(X,Y,Z) = add(multiply(multiply(X,Y),Z),additive_inverse(multiply(X,multiply(Y,Z)))) ).

%----Commutator
cnf(commutator,axiom,
    commutator(X,Y) = add(multiply(Y,X),additive_inverse(multiply(X,Y))) ).

%--------------------------------------------------------------------------

```

### ./RNG004-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : RNG004-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Ring Theory (Alternative)
% Axioms   : Alternative ring theory (equality) axioms
% Version  : [AH90] (equality) axioms.
% English  :

% Refs     : [AH90]  Anantharaman & Hsiang (1990), Automated Proofs of the
% Source   : [AH90]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   17 (  15 unt;   0 nHn;   3 RR)
%            Number of literals    :   19 (  19 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   32 (   2 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%----There exists an additive identity element [1]
cnf(left_additive_identity,axiom,
    add(additive_identity,X) = X ).

%----Multiplicative identity [2] & [3]
cnf(left_multiplicative_zero,axiom,
    multiply(additive_identity,X) = additive_identity ).

cnf(right_multiplicative_zero,axiom,
    multiply(X,additive_identity) = additive_identity ).

%----Addition of inverse [4]
cnf(add_inverse,axiom,
    add(additive_inverse(X),X) = additive_identity ).

%----Sum of inverses [5]
cnf(sum_of_inverses,axiom,
    additive_inverse(add(X,Y)) = add(additive_inverse(X),additive_inverse(Y)) ).

%----Inverse of additive_inverse of X is X [6]
cnf(additive_inverse_additive_inverse,axiom,
    additive_inverse(additive_inverse(X)) = X ).

%----Distribution of multiply over add [7] & [8]
cnf(multiply_over_add1,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(multiply_over_add2,axiom,
    multiply(add(X,Y),Z) = add(multiply(X,Z),multiply(Y,Z)) ).

%----Right alternative law [9]
cnf(right_alternative,axiom,
    multiply(multiply(X,Y),Y) = multiply(X,multiply(Y,Y)) ).

%----Left alternative law [10]
cnf(left_alternative,axiom,
    multiply(multiply(X,X),Y) = multiply(X,multiply(X,Y)) ).

%----Inverse and product [11] & [12]
cnf(inverse_product1,axiom,
    multiply(additive_inverse(X),Y) = additive_inverse(multiply(X,Y)) ).

cnf(inverse_product2,axiom,
    multiply(X,additive_inverse(Y)) = additive_inverse(multiply(X,Y)) ).

%----Inverse of additive identity [13]
cnf(inverse_additive_identity,axiom,
    additive_inverse(additive_identity) = additive_identity ).

%----Commutativity for addition
cnf(commutativity_for_addition,axiom,
    add(X,Y) = add(Y,X) ).

%----Associativity for addition
cnf(associativity_for_addition,axiom,
    add(X,add(Y,Z)) = add(add(X,Y),Z) ).

%----Left and right cancellation for addition
cnf(left_cancellation_for_addition,axiom,
    ( add(X,Z) != add(Y,Z)
    | X = Y ) ).

cnf(right_cancellation_for_addition,axiom,
    ( add(Z,X) != add(Z,Y)
    | X = Y ) ).

%--------------------------------------------------------------------------

```

### ./RNG005-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : RNG005-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Ring Theory
% Axioms   : Ring theory (equality) axioms
% Version  : [LW92] (equality) axioms.
% English  :

% Refs     : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit
% Source   : [LW92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    9 (   9 unt;   0 nHn;   0 RR)
%            Number of literals    :    9 (   9 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   18 (   0 sgn)
% SPC      : 

% Comments : These axioms are used in [Wos88] p.203.
%--------------------------------------------------------------------------
%----There exists an additive identity element
cnf(left_additive_identity,axiom,
    add(additive_identity,X) = X ).

cnf(right_additive_identity,axiom,
    add(X,additive_identity) = X ).

%----Existence of left additive additive_inverse
cnf(left_additive_inverse,axiom,
    add(additive_inverse(X),X) = additive_identity ).

cnf(right_additive_inverse,axiom,
    add(X,additive_inverse(X)) = additive_identity ).

%----Associativity for addition
cnf(associativity_for_addition,axiom,
    add(X,add(Y,Z)) = add(add(X,Y),Z) ).

%----Commutativity for addition
cnf(commutativity_for_addition,axiom,
    add(X,Y) = add(Y,X) ).

%----Associativity for multiplication
cnf(associativity_for_multiplication,axiom,
    multiply(X,multiply(Y,Z)) = multiply(multiply(X,Y),Z) ).

%----Distributive property of product over sum
cnf(distribute1,axiom,
    multiply(X,add(Y,Z)) = add(multiply(X,Y),multiply(X,Z)) ).

cnf(distribute2,axiom,
    multiply(add(X,Y),Z) = add(multiply(X,Z),multiply(Y,Z)) ).

%--------------------------------------------------------------------------

```

## Robbins Algebra

### ./ROB001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : ROB001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Robbins algebra
% Axioms   : Robbins algebra axioms
% Version  : [Win90] (equality) axioms.
% English  :

% Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras
%          : [Win90] Winker (1990), Robbins Algebra: Conditions that make a
% Source   : [OTTER]
% Names    : Lemma 2.2 [Win90]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   0 RR)
%            Number of literals    :    3 (   3 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 1-2 aty)
%            Number of variables   :    7 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(commutativity_of_add,axiom,
    add(X,Y) = add(Y,X) ).

cnf(associativity_of_add,axiom,
    add(add(X,Y),Z) = add(X,add(Y,Z)) ).

cnf(robbins_axiom,axiom,
    negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))) = X ).

%--------------------------------------------------------------------------

```

### ./ROB001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : ROB001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Robbins Algebra
% Axioms   : Robbins algebra numbers axioms
% Version  : [Win90] (equality) axioms.
% English  :

% Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras
%          : [Win90] Winker (1990), Robbins Algebra: Conditions that make a
% Source   : [Win90]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    4 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   2 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : 

% Comments : Requires ROB001-0.ax
%--------------------------------------------------------------------------
cnf(one_times_x,axiom,
    multiply(one,X) = X ).

cnf(times_by_adding,axiom,
    ( ~ positive_integer(X)
    | multiply(successor(V),X) = add(X,multiply(V,X)) ) ).

cnf(one,axiom,
    positive_integer(one) ).

cnf(next_integer,axiom,
    ( ~ positive_integer(X)
    | positive_integer(successor(X)) ) ).

%--------------------------------------------------------------------------

```
## Set Theory
### ./SET001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Membership and subsets
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   1 nHn;   5 RR)
%            Number of literals    :   14 (   0 equ;   7 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   13 (   0 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
cnf(membership_in_subsets,axiom,
    ( ~ member(Element,Subset)
    | ~ subset(Subset,Superset)
    | member(Element,Superset) ) ).

cnf(subsets_axiom1,axiom,
    ( subset(Subset,Superset)
    | member(member_of_1_not_of_2(Subset,Superset),Subset) ) ).

cnf(subsets_axiom2,axiom,
    ( ~ member(member_of_1_not_of_2(Subset,Superset),Superset)
    | subset(Subset,Superset) ) ).

cnf(set_equal_sets_are_subsets1,axiom,
    ( ~ equal_sets(Subset,Superset)
    | subset(Subset,Superset) ) ).

cnf(set_equal_sets_are_subsets2,axiom,
    ( ~ equal_sets(Superset,Subset)
    | subset(Subset,Superset) ) ).

cnf(subsets_are_set_equal_sets,axiom,
    ( ~ subset(Set1,Set2)
    | ~ subset(Set2,Set1)
    | equal_sets(Set2,Set1) ) ).

%--------------------------------------------------------------------------

```

### ./SET001-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET001-1 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Membership and union
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    : Problem 118 [LS74]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   2 nHn;   5 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   21 (   2 sgn)
% SPC      : 

% Comments : Requires SET001-0.ax
%--------------------------------------------------------------------------
cnf(member_of_union_is_member_of_one_set,axiom,
    ( ~ union(Set1,Set2,Union)
    | ~ member(Element,Union)
    | member(Element,Set1)
    | member(Element,Set2) ) ).

cnf(member_of_set1_is_member_of_union,axiom,
    ( ~ union(Set1,Set2,Union)
    | ~ member(Element,Set1)
    | member(Element,Union) ) ).

cnf(member_of_set2_is_member_of_union,axiom,
    ( ~ union(Set1,Set2,Union)
    | ~ member(Element,Set2)
    | member(Element,Union) ) ).

cnf(union_axiom1,axiom,
    ( union(Set1,Set2,Union)
    | member(g(Set1,Set2,Union),Set1)
    | member(g(Set1,Set2,Union),Set2)
    | member(g(Set1,Set2,Union),Union) ) ).

cnf(union_axiom2,axiom,
    ( ~ member(g(Set1,Set2,Union),Set1)
    | ~ member(g(Set1,Set2,Union),Union)
    | union(Set1,Set2,Union) ) ).

cnf(union_axiom3,axiom,
    ( ~ member(g(Set1,Set2,Union),Set2)
    | ~ member(g(Set1,Set2,Union),Union)
    | union(Set1,Set2,Union) ) ).

%--------------------------------------------------------------------------

```

### ./SET001-2.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET001-2 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Membership and intersection
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    : Problem 118 [LS74]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   2 nHn;   4 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   21 (   2 sgn)
% SPC      : 

% Comments : Requires SET001-0.ax
%--------------------------------------------------------------------------
cnf(member_of_intersection_is_member_of_set1,axiom,
    ( ~ intersection(Set1,Set2,Intersection)
    | ~ member(Element,Intersection)
    | member(Element,Set1) ) ).

cnf(member_of_intersection_is_member_of_set2,axiom,
    ( ~ intersection(Set1,Set2,Intersection)
    | ~ member(Element,Intersection)
    | member(Element,Set2) ) ).

cnf(member_of_both_is_member_of_intersection,axiom,
    ( ~ intersection(Set1,Set2,Intersection)
    | ~ member(Element,Set2)
    | ~ member(Element,Set1)
    | member(Element,Intersection) ) ).

cnf(intersection_axiom1,axiom,
    ( member(h(Set1,Set2,Intersection),Intersection)
    | intersection(Set1,Set2,Intersection)
    | member(h(Set1,Set2,Intersection),Set1) ) ).

cnf(intersection_axiom2,axiom,
    ( member(h(Set1,Set2,Intersection),Intersection)
    | intersection(Set1,Set2,Intersection)
    | member(h(Set1,Set2,Intersection),Set2) ) ).

cnf(intersection_axiom3,axiom,
    ( ~ member(h(Set1,Set2,Intersection),Intersection)
    | ~ member(h(Set1,Set2,Intersection),Set2)
    | ~ member(h(Set1,Set2,Intersection),Set1)
    | intersection(Set1,Set2,Intersection) ) ).

%--------------------------------------------------------------------------

```

### ./SET001-3.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET001-3 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Membership and difference
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   0 unt;   4 nHn;   5 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   21 (   2 sgn)
% SPC      : 

% Comments : Requires SET001-0.ax
%--------------------------------------------------------------------------
cnf(member_of_difference,axiom,
    ( ~ difference(Set1,Set2,Difference)
    | ~ member(Element,Difference)
    | member(Element,Set1) ) ).

cnf(not_member_of_difference,axiom,
    ( ~ member(Element,Set1)
    | ~ member(Element,Set2)
    | ~ difference(A_set,Set1,Set2) ) ).

cnf(member_of_difference_or_set2,axiom,
    ( ~ member(Element,Set1)
    | ~ difference(Set1,Set2,Difference)
    | member(Element,Difference)
    | member(Element,Set2) ) ).

cnf(difference_axiom2,axiom,
    ( difference(Set1,Set2,Difference)
    | member(k(Set1,Set2,Difference),Set1)
    | member(k(Set1,Set2,Difference),Difference) ) ).

cnf(difference_axiom1,axiom,
    ( ~ member(k(Set1,Set2,Difference),Set2)
    | member(k(Set1,Set2,Difference),Difference)
    | difference(Set1,Set2,Difference) ) ).

cnf(difference_axiom3,axiom,
    ( ~ member(k(Set1,Set2,Difference),Difference)
    | ~ member(k(Set1,Set2,Difference),Set1)
    | member(k(Set1,Set2,Difference),Set2)
    | difference(Set1,Set2,Difference) ) ).

%--------------------------------------------------------------------------

```

### ./SET002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Set theory axioms
% Version  : [MOW76] axioms : Biased.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   21 (   3 unt;   3 nHn;  15 RR)
%            Number of literals    :   45 (   0 equ;  23 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-2 aty)
%            Number of variables   :   48 (   5 sgn)
% SPC      : 

% Comments :
%--------------------------------------------------------------------------
%-----Definition of the empty set.
cnf(empty_set,axiom,
    ~ member(X,empty_set) ).

%-----Subset axioms. These are the same as in SET001-0.ax
cnf(membership_in_subsets,axiom,
    ( ~ member(Element,Subset)
    | ~ subset(Subset,Superset)
    | member(Element,Superset) ) ).

cnf(subsets_axiom1,axiom,
    ( subset(Subset,Superset)
    | member(member_of_1_not_of_2(Subset,Superset),Subset) ) ).

cnf(subsets_axiom2,axiom,
    ( ~ member(member_of_1_not_of_2(Subset,Superset),Superset)
    | subset(Subset,Superset) ) ).

%-----Axioms of complementation.
cnf(member_of_set_or_complement,axiom,
    ( member(X,Xs)
    | member(X,complement(Xs)) ) ).

cnf(not_member_of_set_and_complement,axiom,
    ( ~ member(X,Xs)
    | ~ member(X,complement(Xs)) ) ).

%-----Axioms of union.
cnf(member_of_set1_is_member_of_union,axiom,
    ( ~ member(X,Xs)
    | member(X,union(Xs,Ys)) ) ).

cnf(member_of_set2_is_member_of_union,axiom,
    ( ~ member(X,Ys)
    | member(X,union(Xs,Ys)) ) ).

cnf(member_of_union_is_member_of_one_set,axiom,
    ( ~ member(X,union(Xs,Ys))
    | member(X,Xs)
    | member(X,Ys) ) ).

%-----Axioms of intersection.
cnf(member_of_both_is_member_of_intersection,axiom,
    ( ~ member(X,Xs)
    | ~ member(X,Ys)
    | member(X,intersection(Xs,Ys)) ) ).

cnf(member_of_intersection_is_member_of_set1,axiom,
    ( ~ member(X,intersection(Xs,Ys))
    | member(X,Xs) ) ).

cnf(member_of_intersection_is_member_of_set2,axiom,
    ( ~ member(X,intersection(Xs,Ys))
    | member(X,Ys) ) ).

%-----Set equality axioms.
cnf(set_equal_sets_are_subsets1,axiom,
    ( ~ equal_sets(Subset,Superset)
    | subset(Subset,Superset) ) ).

cnf(set_equal_sets_are_subsets2,axiom,
    ( ~ equal_sets(Superset,Subset)
    | subset(Subset,Superset) ) ).

cnf(subsets_are_set_equal_sets,axiom,
    ( ~ subset(Set1,Set2)
    | ~ subset(Set2,Set1)
    | equal_sets(Set2,Set1) ) ).

%-----Equality axioms.
cnf(reflexivity_for_set_equal,axiom,
    equal_sets(Xs,Xs) ).

cnf(symmetry_for_set_equal,axiom,
    ( ~ equal_sets(Xs,Ys)
    | equal_sets(Ys,Xs) ) ).

cnf(transitivity_for_set_equal,axiom,
    ( ~ equal_sets(Xs,Ys)
    | ~ equal_sets(Ys,Zs)
    | equal_sets(Xs,Zs) ) ).

cnf(reflexivity_for_equal_elements,axiom,
    equal_elements(X,X) ).

cnf(symmetry_for_equal_elements,axiom,
    ( ~ equal_elements(X,Y)
    | equal_elements(Y,X) ) ).

cnf(transitivity_for_equal_elements,axiom,
    ( ~ equal_elements(X,Y)
    | ~ equal_elements(Y,Z)
    | equal_elements(X,Z) ) ).

%--------------------------------------------------------------------------

```

### ./SET003-0.ax

```
%--------------------------------------------------------------------------
% File     : SET003-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Set Theory
% Axioms   : Set theory axioms based on Godel set theory
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :  141 (  11 unt;  20 nHn; 118 RR)
%            Number of literals    :  355 (  47 equ; 197 neg)
%            Maximal clause size   :    8 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :   14 (  13 usr;   0 prp; 1-5 aty)
%            Number of functors    :   59 (  59 usr;   6 con; 0-5 aty)
%            Number of variables   :  320 (  28 sgn)
% SPC      : 

% Comments : Requires EQU001-0.ax
%          : These axioms are based on Godel's axioms for set theory.
%          : These axioms are also used in [Wos88] p.225.
%--------------------------------------------------------------------------
%----Axiom A-1, little sets are sets (omitted because all objects are sets)

%----Axiom A-2, elements of sets are little sets.
cnf(a2,axiom,
    ( ~ member(X,Y)
    | little_set(X) ) ).

%----Axiom A-3, principle of extensionality
cnf(extensionality1,axiom,
    ( little_set(f1(X,Y))
    | X = Y ) ).

cnf(extensionality2,axiom,
    ( member(f1(X,Y),X)
    | member(f1(X,Y),Y)
    | X = Y ) ).

cnf(extensionality3,axiom,
    ( ~ member(f1(X,Y),X)
    | ~ member(f1(X,Y),Y)
    | X = Y ) ).

%----Axiom a-4, existence of nonordered pair
cnf(non_ordered_pair1,axiom,
    ( ~ member(U,non_ordered_pair(X,Y))
    | U = X
    | U = Y ) ).

cnf(non_ordered_pair2,axiom,
    ( member(U,non_ordered_pair(X,Y))
    | ~ little_set(U)
    | U != X ) ).

cnf(non_ordered_pair3,axiom,
    ( member(U,non_ordered_pair(X,Y))
    | ~ little_set(U)
    | U != Y ) ).

cnf(non_ordered_pair4,axiom,
    little_set(non_ordered_pair(X,Y)) ).

%----Definition of singleton set
cnf(singleton_set,axiom,
    singleton_set(X) = non_ordered_pair(X,X) ).

%----Definition of ordered pair
cnf(ordered_pair,axiom,
    ordered_pair(X,Y) = non_ordered_pair(singleton_set(X),non_ordered_pair(X,Y)) ).

%----Definition of ordered pair predicate
cnf(ordered_pair_predicate1,axiom,
    ( ~ ordered_pair_predicate(X)
    | little_set(f2(X)) ) ).

cnf(ordered_pair_predicate2,axiom,
    ( ~ ordered_pair_predicate(X)
    | little_set(f3(X)) ) ).

cnf(ordered_pair_predicate3,axiom,
    ( ~ ordered_pair_predicate(X)
    | X = ordered_pair(f2(X),f3(X)) ) ).

cnf(ordered_pair_predicate4,axiom,
    ( ordered_pair_predicate(X)
    | ~ little_set(Y)
    | ~ little_set(Z)
    | X != ordered_pair(Y,Z) ) ).

%----Axiom of first
cnf(first1,axiom,
    ( ~ member(Z,first(X))
    | little_set(f4(Z,X)) ) ).

cnf(first2,axiom,
    ( ~ member(Z,first(X))
    | little_set(f5(Z,X)) ) ).

cnf(first3,axiom,
    ( ~ member(Z,first(X))
    | X = ordered_pair(f4(Z,X),f5(Z,X)) ) ).

cnf(first4,axiom,
    ( ~ member(Z,first(X))
    | member(Z,f4(Z,X)) ) ).

cnf(first5,axiom,
    ( member(Z,first(X))
    | ~ little_set(U)
    | ~ little_set(V)
    | X != ordered_pair(U,V)
    | ~ member(Z,U) ) ).

%----Axiom of second
cnf(second1,axiom,
    ( ~ member(Z,second(X))
    | little_set(f6(Z,X)) ) ).

cnf(second2,axiom,
    ( ~ member(Z,second(X))
    | little_set(f7(Z,X)) ) ).

cnf(second3,axiom,
    ( ~ member(Z,second(X))
    | X = ordered_pair(f6(Z,X),f7(Z,X)) ) ).

cnf(second4,axiom,
    ( ~ member(Z,second(X))
    | member(Z,f7(Z,X)) ) ).

cnf(second5,axiom,
    ( member(Z,second(X))
    | ~ little_set(U)
    | ~ little_set(V)
    | X != ordered_pair(U,V)
    | ~ member(Z,V) ) ).

%----Axiom B-1, element relation
cnf(element_relation1,axiom,
    ( ~ member(Z,estin)
    | ordered_pair_predicate(Z) ) ).

cnf(element_relation2,axiom,
    ( ~ member(Z,estin)
    | member(first(Z),second(Z)) ) ).

cnf(element_relation3,axiom,
    ( member(Z,estin)
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Z)
    | ~ member(first(Z),second(Z)) ) ).

%----Axiom B-2, intersection
cnf(intersection1,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,X) ) ).

cnf(intersection2,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,Y) ) ).

cnf(intersection3,axiom,
    ( member(Z,intersection(X,Y))
    | ~ member(Z,X)
    | ~ member(Z,Y) ) ).

%----Axiom B-3, complement
cnf(complement1,axiom,
    ( ~ member(Z,complement(X))
    | ~ member(Z,X) ) ).

cnf(complement2,axiom,
    ( member(Z,complement(X))
    | ~ little_set(Z)
    | member(Z,X) ) ).

%----Definition of union
cnf(union,axiom,
    union(X,Y) = complement(intersection(complement(X),complement(Y))) ).

%----Axiom B-4, domain
cnf(domain1,axiom,
    ( ~ member(Z,domain_of(X))
    | ordered_pair_predicate(f8(Z,X)) ) ).

cnf(domain2,axiom,
    ( ~ member(Z,domain_of(X))
    | member(f8(Z,X),X) ) ).

cnf(domain3,axiom,
    ( ~ member(Z,domain_of(X))
    | Z = first(f8(Z,X)) ) ).

cnf(domain4,axiom,
    ( member(Z,domain_of(X))
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Xp)
    | ~ member(Xp,X)
    | Z != first(Xp) ) ).

%----Axiom B-5, cross product
cnf(cross_product1,axiom,
    ( ~ member(Z,cross_product(X,Y))
    | ordered_pair_predicate(Z) ) ).

cnf(cross_product2,axiom,
    ( ~ member(Z,cross_product(X,Y))
    | member(first(Z),X) ) ).

cnf(cross_product3,axiom,
    ( ~ member(Z,cross_product(X,Y))
    | member(second(Z),Y) ) ).

cnf(cross_product4,axiom,
    ( member(Z,cross_product(X,Y))
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Z)
    | ~ member(first(Z),X)
    | ~ member(second(Z),Y) ) ).

%----Axiom B-6, converse
cnf(converse1,axiom,
    ( ~ member(Z,converse(X))
    | ordered_pair_predicate(Z) ) ).

cnf(converse2,axiom,
    ( ~ member(Z,converse(X))
    | member(ordered_pair(second(Z),first(Z)),X) ) ).

cnf(converse3,axiom,
    ( member(Z,converse(X))
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Z)
    | ~ member(ordered_pair(second(Z),first(Z)),X) ) ).

%----Axiom B-7, rotate_right
cnf(rotate_right1,axiom,
    ( ~ member(Z,rotate_right(X))
    | little_set(f9(Z,X)) ) ).

cnf(rotate_right2,axiom,
    ( ~ member(Z,rotate_right(X))
    | little_set(f10(Z,X)) ) ).

cnf(rotate_right3,axiom,
    ( ~ member(Z,rotate_right(X))
    | little_set(f11(Z,X)) ) ).

cnf(rotate_right4,axiom,
    ( ~ member(Z,rotate_right(X))
    | Z = ordered_pair(f9(Z,X),ordered_pair(f10(Z,X),f11(Z,X))) ) ).

cnf(rotate_right5,axiom,
    ( ~ member(Z,rotate_right(X))
    | member(ordered_pair(f10(Z,X),ordered_pair(f11(Z,X),f9(Z,X))),X) ) ).

cnf(rotate_right6,axiom,
    ( member(Z,rotate_right(X))
    | ~ little_set(Z)
    | ~ little_set(U)
    | ~ little_set(V)
    | ~ little_set(W)
    | Z != ordered_pair(U,ordered_pair(V,W))
    | ~ member(ordered_pair(V,ordered_pair(W,U)),X) ) ).

%----Axiom B-8, flip_range
cnf(flip_range1,axiom,
    ( ~ member(Z,flip_range_of(X))
    | little_set(f12(Z,X)) ) ).

cnf(flip_range2,axiom,
    ( ~ member(Z,flip_range_of(X))
    | little_set(f13(Z,X)) ) ).

cnf(flip_range3,axiom,
    ( ~ member(Z,flip_range_of(X))
    | little_set(f14(Z,X)) ) ).

cnf(flip_range4,axiom,
    ( ~ member(Z,flip_range_of(X))
    | Z = ordered_pair(f12(Z,X),ordered_pair(f13(Z,X),f14(Z,X))) ) ).

cnf(flip_range5,axiom,
    ( ~ member(Z,flip_range_of(X))
    | member(ordered_pair(f12(Z,X),ordered_pair(f14(Z,X),f13(Z,X))),X) ) ).

cnf(flip_range6,axiom,
    ( member(Z,flip_range_of(X))
    | ~ little_set(Z)
    | ~ little_set(U)
    | ~ little_set(V)
    | ~ little_set(W)
    | Z != ordered_pair(U,ordered_pair(V,W))
    | ~ member(ordered_pair(U,ordered_pair(W,V)),X) ) ).

%----Definition of successor
cnf(successor,axiom,
    successor(X) = union(X,singleton_set(X)) ).

%----Definition of empty set
cnf(empty_set,axiom,
    ~ member(Z,empty_set) ).

%----Definition of universal set
cnf(universal_set,axiom,
    ( member(Z,universal_set)
    | ~ little_set(Z) ) ).

%----Axiom C-1, infinity
cnf(infinity1,axiom,
    little_set(infinity) ).

cnf(infinity2,axiom,
    member(empty_set,infinity) ).

cnf(infinity3,axiom,
    ( ~ member(X,infinity)
    | member(successor(X),infinity) ) ).

%----Axiom C-2, sigma (union of elements)
cnf(sigma1,axiom,
    ( ~ member(Z,sigma(X))
    | member(f16(Z,X),X) ) ).

cnf(sigma2,axiom,
    ( ~ member(Z,sigma(X))
    | member(Z,f16(Z,X)) ) ).

cnf(sigma3,axiom,
    ( member(Z,sigma(X))
    | ~ member(Y,X)
    | ~ member(Z,Y) ) ).

cnf(sigma4,axiom,
    ( ~ little_set(U)
    | little_set(sigma(U)) ) ).

%----Definition of subset
cnf(subset1,axiom,
    ( ~ subset(X,Y)
    | ~ member(U,X)
    | member(U,Y) ) ).

cnf(subset2,axiom,
    ( subset(X,Y)
    | member(f17(X,Y),X) ) ).

cnf(subset3,axiom,
    ( subset(X,Y)
    | ~ member(f17(X,Y),Y) ) ).

%----Definition of proper subset
cnf(proper_subset1,axiom,
    ( ~ proper_subset(X,Y)
    | subset(X,Y) ) ).

cnf(proper_subset2,axiom,
    ( ~ proper_subset(X,Y)
    | X != Y ) ).

cnf(proper_subset3,axiom,
    ( proper_subset(X,Y)
    | ~ subset(X,Y)
    | X = Y ) ).

%----Axiom C-3, powerset
cnf(powerset1,axiom,
    ( ~ member(Z,powerset(X))
    | subset(Z,X) ) ).

cnf(powerset2,axiom,
    ( member(Z,powerset(X))
    | ~ little_set(Z)
    | ~ subset(Z,X) ) ).

cnf(powerset3,axiom,
    ( ~ little_set(U)
    | little_set(powerset(U)) ) ).

%----Definition of relation
cnf(relation1,axiom,
    ( ~ relation(Z)
    | ~ member(X,Z)
    | ordered_pair_predicate(X) ) ).

cnf(relation2,axiom,
    ( relation(Z)
    | member(f18(Z),Z) ) ).

cnf(relation3,axiom,
    ( relation(Z)
    | ~ ordered_pair_predicate(f18(Z)) ) ).

%----Definition of single-valued set
cnf(single_valued_set1,axiom,
    ( ~ single_valued_set(X)
    | ~ little_set(U)
    | ~ little_set(V)
    | ~ little_set(W)
    | ~ member(ordered_pair(U,V),X)
    | ~ member(ordered_pair(U,W),X)
    | V = W ) ).

cnf(single_valued_set2,axiom,
    ( single_valued_set(X)
    | little_set(f19(X)) ) ).

cnf(single_valued_set3,axiom,
    ( single_valued_set(X)
    | little_set(f20(X)) ) ).

cnf(single_valued_set4,axiom,
    ( single_valued_set(X)
    | little_set(f21(X)) ) ).

cnf(single_valued_set5,axiom,
    ( single_valued_set(X)
    | member(ordered_pair(f19(X),f20(X)),X) ) ).

cnf(single_valued_set6,axiom,
    ( single_valued_set(X)
    | member(ordered_pair(f19(X),f21(X)),X) ) ).

cnf(single_valued_set7,axiom,
    ( single_valued_set(X)
    | f20(X) != f21(X) ) ).

%----Definition of function
cnf(function1,axiom,
    ( ~ function(Xf)
    | relation(Xf) ) ).

cnf(function2,axiom,
    ( ~ function(Xf)
    | single_valued_set(Xf) ) ).

cnf(function3,axiom,
    ( function(Xf)
    | ~ relation(Xf)
    | ~ single_valued_set(Xf) ) ).

%----Axiom C-4, image and substitution
cnf(image_and_substitution1,axiom,
    ( ~ member(Z,image(X,Xf))
    | ordered_pair_predicate(f22(Z,X,Xf)) ) ).

cnf(image_and_substitution2,axiom,
    ( ~ member(Z,image(X,Xf))
    | member(f22(Z,X,Xf),Xf) ) ).

cnf(image_and_substitution3,axiom,
    ( ~ member(Z,image(X,Xf))
    | member(first(f22(Z,X,Xf)),X) ) ).

cnf(image_and_substitution4,axiom,
    ( ~ member(Z,image(X,Xf))
    | second(f22(Z,X,Xf)) = Z ) ).

cnf(image_and_substitution5,axiom,
    ( member(Z,image(X,Xf))
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Y)
    | ~ member(Y,Xf)
    | ~ member(first(Y),X)
    | second(Y) != Z ) ).

cnf(image_and_substitution6,axiom,
    ( ~ little_set(X)
    | ~ function(Xf)
    | little_set(image(X,Xf)) ) ).

%----Definition of disjoint
cnf(disjoint1,axiom,
    ( ~ disjoint(X,Y)
    | ~ member(U,X)
    | ~ member(U,Y) ) ).

cnf(disjoint2,axiom,
    ( disjoint(X,Y)
    | member(f23(X,Y),X) ) ).

cnf(disjoint3,axiom,
    ( disjoint(X,Y)
    | member(f23(X,Y),Y) ) ).

%----Axiom D, regularity
cnf(regularity1,axiom,
    ( X = empty_set
    | member(f24(X),X) ) ).

cnf(regularity2,axiom,
    ( X = empty_set
    | disjoint(f24(X),X) ) ).

%----Axiom E, choice
cnf(choice1,axiom,
    function(f25) ).

cnf(choice2,axiom,
    ( ~ little_set(X)
    | X = empty_set
    | member(f26(X),X) ) ).

cnf(choice3,axiom,
    ( ~ little_set(X)
    | X = empty_set
    | member(ordered_pair(X,f26(X)),f25) ) ).

%----Definition of range_of
cnf(range_of1,axiom,
    ( ~ member(Z,range_of(X))
    | ordered_pair_predicate(f27(Z,X)) ) ).

cnf(range_of2,axiom,
    ( ~ member(Z,range_of(X))
    | member(f27(Z,X),X) ) ).

cnf(range_of3,axiom,
    ( ~ member(Z,range_of(X))
    | Z = second(f27(Z,X)) ) ).

cnf(range_of4,axiom,
    ( member(Z,range_of(X))
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Xp)
    | ~ member(Xp,X)
    | Z != second(Xp) ) ).

%----Definition of identity relation
cnf(identity_relation1,axiom,
    ( ~ member(Z,identity_relation)
    | ordered_pair_predicate(Z) ) ).

cnf(identity_relation2,axiom,
    ( ~ member(Z,identity_relation)
    | first(Z) = second(Z) ) ).

cnf(identity_relation3,axiom,
    ( member(Z,identity_relation)
    | ~ little_set(Z)
    | ~ ordered_pair_predicate(Z)
    | first(Z) != second(Z) ) ).

%----Definition of restrict
cnf(restrict,axiom,
    restrict(X,Y) = intersection(X,cross_product(Y,universal_set)) ).

%----Definition of one-to-one function
cnf(one_to_one_function1,axiom,
    ( ~ one_to_one_function(Xf)
    | function(Xf) ) ).

cnf(one_to_one_function2,axiom,
    ( ~ one_to_one_function(Xf)
    | function(converse(Xf)) ) ).

cnf(one_to_one_function3,axiom,
    ( one_to_one_function(Xf)
    | ~ function(Xf)
    | ~ function(converse(Xf)) ) ).

%----Definition of apply
cnf(apply1,axiom,
    ( ~ member(Z,apply(Xf,Y))
    | ordered_pair_predicate(f28(Z,Xf,Y)) ) ).

cnf(apply2,axiom,
    ( ~ member(Z,apply(Xf,Y))
    | member(f28(Z,Xf,Y),Xf) ) ).

cnf(apply3,axiom,
    ( ~ member(Z,apply(Xf,Y))
    | first(f28(Z,Xf,Y)) = Y ) ).

cnf(apply4,axiom,
    ( ~ member(Z,apply(Xf,Y))
    | member(Z,second(f28(Z,Xf,Y))) ) ).

cnf(apply5,axiom,
    ( member(Z,apply(Xf,Y))
    | ~ ordered_pair_predicate(W)
    | ~ member(W,Xf)
    | first(W) != Y
    | ~ member(Z,second(W)) ) ).

%----Definition of apply to 2 arguments
cnf(apply_to_two_arguments,axiom,
    apply_to_two_arguments(Xf,X,Y) = apply(Xf,ordered_pair(X,Y)) ).

%----Definition of maps
cnf(maps1,axiom,
    ( ~ maps(Xf,X,Y)
    | function(Xf) ) ).

cnf(maps2,axiom,
    ( ~ maps(Xf,X,Y)
    | domain_of(Xf) = X ) ).

cnf(maps3,axiom,
    ( ~ maps(Xf,X,Y)
    | subset(range_of(Xf),Y) ) ).

cnf(maps4,axiom,
    ( maps(Xf,X,Y)
    | ~ function(Xf)
    | domain_of(Xf) != X
    | ~ subset(range_of(Xf),Y) ) ).

%----Definition of closed
cnf(closed1,axiom,
    ( ~ closed(Xs,Xf)
    | little_set(Xs) ) ).

cnf(closed2,axiom,
    ( ~ closed(Xs,Xf)
    | little_set(Xf) ) ).

cnf(closed3,axiom,
    ( ~ closed(Xs,Xf)
    | maps(Xf,cross_product(Xs,Xs),Xs) ) ).

cnf(closed4,axiom,
    ( closed(Xs,Xf)
    | ~ little_set(Xs)
    | ~ little_set(Xf)
    | ~ maps(Xf,cross_product(Xs,Xs),Xs) ) ).

%----Definition of compose
cnf(compose1,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | little_set(f29(Z,Xf,Xg)) ) ).

cnf(compose2,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | little_set(f30(Z,Xf,Xg)) ) ).

cnf(compose3,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | little_set(f31(Z,Xf,Xg)) ) ).

cnf(compose4,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | Z = ordered_pair(f29(Z,Xf,Xg),f30(Z,Xf,Xg)) ) ).

cnf(compose5,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | member(ordered_pair(f29(Z,Xf,Xg),f31(Z,Xf,Xg)),Xf) ) ).

cnf(compose6,axiom,
    ( ~ member(Z,compose(Xf,Xg))
    | member(ordered_pair(f31(Z,Xf,Xg),f30(Z,Xf,Xg)),Xg) ) ).

cnf(compose7,axiom,
    ( member(Z,compose(Xf,Xg))
    | ~ little_set(Z)
    | ~ little_set(X)
    | ~ little_set(Y)
    | ~ little_set(W)
    | Z != ordered_pair(X,Y)
    | ~ member(ordered_pair(X,W),Xf)
    | ~ member(ordered_pair(W,Y),Xg) ) ).

%----Definition of a homomorphism
cnf(homomorphism1,axiom,
    ( ~ homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | closed(Xs1,Xf1) ) ).

cnf(homomorphism2,axiom,
    ( ~ homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | closed(Xs2,Xf2) ) ).

cnf(homomorphism3,axiom,
    ( ~ homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | maps(Xh,Xs1,Xs2) ) ).

cnf(homomorphism4,axiom,
    ( ~ homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | ~ member(X,Xs1)
    | ~ member(Y,Xs1)
    | apply(Xh,apply_to_two_arguments(Xf1,X,Y)) = apply_to_two_arguments(Xf2,apply(Xh,X),apply(Xh,Y)) ) ).

cnf(homomorphism5,axiom,
    ( homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | ~ closed(Xs1,Xf1)
    | ~ closed(Xs2,Xf2)
    | ~ maps(Xh,Xs1,Xs2)
    | member(f32(Xh,Xs1,Xf1,Xs2,Xf2),Xs1) ) ).

cnf(homomorphism6,axiom,
    ( homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | ~ closed(Xs1,Xf1)
    | ~ closed(Xs2,Xf2)
    | ~ maps(Xh,Xs1,Xs2)
    | member(f33(Xh,Xs1,Xf1,Xs2,Xf2),Xs1) ) ).

cnf(homomorphism7,axiom,
    ( homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)
    | ~ closed(Xs1,Xf1)
    | ~ closed(Xs2,Xf2)
    | ~ maps(Xh,Xs1,Xs2)
    | apply(Xh,apply_to_two_arguments(Xf1,f32(Xh,Xs1,Xf1,Xs2,Xf2),f33(Xh,Xs1,Xf1,Xs2,Xf2))) != apply_to_two_arguments(Xf2,apply(Xh,f32(Xh,Xs1,Xf1,Xs2,Xf2)),apply(Xh,f33(Xh,Xs1,Xf1,Xs2,Xf2))) ) ).

%--------------------------------------------------------------------------
```

### ./SET004-0.ax

```
%--------------------------------------------------------------------------
% File     : SET004-0 : TPTP v8.2.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Axioms   : Set theory axioms based on NBG set theory
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Qua92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   91 (  29 unt;   8 nHn;  62 RR)
%            Number of literals    :  181 (  39 equ;  84 neg)
%            Maximal clause size   :    5 (   1 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number of predicates  :   10 (   9 usr;   0 prp; 1-3 aty)
%            Number of functors    :   38 (  38 usr;   8 con; 0-3 aty)
%            Number of variables   :  176 (  25 sgn)
% SPC      : 

% Comments :
% Bugfixes : v2.1.0 - Clause compatible4 fixed
%--------------------------------------------------------------------------
%----GROUP 1:          AXIOMS AND BASIC DEFINITIONS.

%----Axiom A-1:  sets are classes (omitted because all objects are
%----classes).

%----Definition of < (subclass).
%----a:x:a:y:((x < y) <=> a:u:((u e x) ==> (u e y))).
cnf(subclass_members,axiom,
    ( ~ subclass(X,Y)
    | ~ member(U,X)
    | member(U,Y) ) ).

cnf(not_subclass_members1,axiom,
    ( member(not_subclass_element(X,Y),X)
    | subclass(X,Y) ) ).

cnf(not_subclass_members2,axiom,
    ( ~ member(not_subclass_element(X,Y),Y)
    | subclass(X,Y) ) ).

%----Axiom A-2: elements of classes are sets.
%----a:x:(x < universal_class).
%----Singleton variables OK.
cnf(class_elements_are_sets,axiom,
    subclass(X,universal_class) ).

%----Axiom A-3: principle of extensionality.
%----a:x:a:y:((x = y) <=> (x < y) & (y < x)).
cnf(equal_implies_subclass1,axiom,
    ( X != Y
    | subclass(X,Y) ) ).

cnf(equal_implies_subclass2,axiom,
    ( X != Y
    | subclass(Y,X) ) ).

cnf(subclass_implies_equal,axiom,
    ( ~ subclass(X,Y)
    | ~ subclass(Y,X)
    | X = Y ) ).

%----Axiom A-4: existence of unordered pair.
%----a:u:a:x:a:y:((u e {x, y}) <=> (u e universal_class)
%----& (u = x | u = y)).
%----a:x:a:y:({x, y} e universal_class).
cnf(unordered_pair_member,axiom,
    ( ~ member(U,unordered_pair(X,Y))
    | U = X
    | U = Y ) ).

%----(x e universal_class), (u = x) --> (u e {x, y}).
%----Singleton variables OK.
cnf(unordered_pair2,axiom,
    ( ~ member(X,universal_class)
    | member(X,unordered_pair(X,Y)) ) ).

%----(y e universal_class), (u = y) --> (u e {x, y}).
%----Singleton variables OK.
cnf(unordered_pair3,axiom,
    ( ~ member(Y,universal_class)
    | member(Y,unordered_pair(X,Y)) ) ).

%----Singleton variables OK.
cnf(unordered_pairs_in_universal,axiom,
    member(unordered_pair(X,Y),universal_class) ).

%----Definition of singleton set.
%----a:x:({x} = {x, x}).
cnf(singleton_set,axiom,
    unordered_pair(X,X) = singleton(X) ).

%----See Theorem (SS6) for memb.

%----Definition of ordered pair.
%----a:x:a:y:([x,y] = {{x}, {x, {y}}}).
cnf(ordered_pair,axiom,
    unordered_pair(singleton(X),unordered_pair(X,singleton(Y))) = ordered_pair(X,Y) ).

%----Axiom B-5'a: Cartesian product.
%----a:u:a:v:a:y:(([u,v] e cross_product(x,y)) <=> (u e x) & (v e y)).
%----Singleton variables OK.
cnf(cartesian_product1,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(U,X) ) ).

%----Singleton variables OK.
cnf(cartesian_product2,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(V,Y) ) ).

cnf(cartesian_product3,axiom,
    ( ~ member(U,X)
    | ~ member(V,Y)
    | member(ordered_pair(U,V),cross_product(X,Y)) ) ).

%----See Theorem (OP6) for 1st and 2nd.

%----Axiom B-5'b: Cartesian product.
%----a:z:(z e cross_product(x,y) --> ([first(z),second(z)] = z)
%----Singleton variables OK.
cnf(cartesian_product4,axiom,
    ( ~ member(Z,cross_product(X,Y))
    | ordered_pair(first(Z),second(Z)) = Z ) ).

%----Axiom B-1: E (element relation).
%----(E < cross_product(universal_class,universal_class)).
%----a:x:a:y:(([x,y] e E) <=> ([x,y] e cross_product(universal_class,
%----universal_class)) (x e y)).
cnf(element_relation1,axiom,
    subclass(element_relation,cross_product(universal_class,universal_class)) ).

cnf(element_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),element_relation)
    | member(X,Y) ) ).

cnf(element_relation3,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | ~ member(X,Y)
    | member(ordered_pair(X,Y),element_relation) ) ).

%----Axiom B-2: * (intersection).
%----a:z:a:x:a:y:((z e (x * y)) <=> (z e x) & (z e y)).
%----Singleton variables OK.
cnf(intersection1,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,X) ) ).

%----Singleton variables OK.
cnf(intersection2,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,Y) ) ).

cnf(intersection3,axiom,
    ( ~ member(Z,X)
    | ~ member(Z,Y)
    | member(Z,intersection(X,Y)) ) ).

%----Axiom B-3: complement.
%----a:z:a:x:((z e ~(x)) <=> (z e universal_class) & -(z e x)).
cnf(complement1,axiom,
    ( ~ member(Z,complement(X))
    | ~ member(Z,X) ) ).

cnf(complement2,axiom,
    ( ~ member(Z,universal_class)
    | member(Z,complement(X))
    | member(Z,X) ) ).

%---- Theorem (SP2) introduces the null class O.

%----Definition of + (union).
%----a:x:a:y:((x + y) = ~((~(x) * ~(y)))).
cnf(union,axiom,
    complement(intersection(complement(X),complement(Y))) = union(X,Y) ).

%----Definition of & (exclusive or). (= symmetric difference).
%----a:x:a:y:((x y) = (~(x * y) * ~(~(x) * ~(y)))).
cnf(symmetric_difference,axiom,
    intersection(complement(intersection(X,Y)),complement(intersection(complement(X),complement(Y)))) = symmetric_difference(X,Y) ).

%----Definition of restriction.
%----a:x(restrict(xr,x,y) = (xr * cross_product(x,y))).
%----This is extra to the paper
cnf(restriction1,axiom,
    intersection(Xr,cross_product(X,Y)) = restrict(Xr,X,Y) ).

cnf(restriction2,axiom,
    intersection(cross_product(X,Y),Xr) = restrict(Xr,X,Y) ).

%----Axiom B-4: D (domain_of).
%----a:y:a:z:((z e domain_of(x)) <=> (z e universal_class) &
%---- -(restrict(x,{z},universal_class) = O)).
%----next is subsumed by A-2.
%------> (domain_of(x) < universal_class).
cnf(domain1,axiom,
    ( restrict(X,singleton(Z),universal_class) != null_class
    | ~ member(Z,domain_of(X)) ) ).

cnf(domain2,axiom,
    ( ~ member(Z,universal_class)
    | restrict(X,singleton(Z),universal_class) = null_class
    | member(Z,domain_of(X)) ) ).

%----Axiom B-7: rotate.
%----a:x:(rotate(x) <  cross_product(cross_product(universal_class,
%----universal_class),universal_class)).
%----a:x:a:u:a:v:a:w:(([[u,v],w] e rotate(x)) <=> ([[u,v],w]]
%---- e cross_product(cross_product(universal_class,universal_class),
%----universal_class)) & ([[v,w],u]] e x).
%----Singleton variables OK.
cnf(rotate1,axiom,
    subclass(rotate(X),cross_product(cross_product(universal_class,universal_class),universal_class)) ).

cnf(rotate2,axiom,
    ( ~ member(ordered_pair(ordered_pair(U,V),W),rotate(X))
    | member(ordered_pair(ordered_pair(V,W),U),X) ) ).

cnf(rotate3,axiom,
    ( ~ member(ordered_pair(ordered_pair(V,W),U),X)
    | ~ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
    | member(ordered_pair(ordered_pair(U,V),W),rotate(X)) ) ).

%----Axiom B-8: flip.
%----a:x:(flip(x) <  cross_product(cross_product(universal_class,
%----universal_class),universal_class)).
%----a:z:a:u:a:v:a:w:(([[u,v],w] e flip(x)) <=> ([[u,v],w]
%----e cross_product(cross_product(universal_class,universal_class),
%----universal_class)) & ([[v,u],w] e x).
%----Singleton variables OK.
cnf(flip1,axiom,
    subclass(flip(X),cross_product(cross_product(universal_class,universal_class),universal_class)) ).

cnf(flip2,axiom,
    ( ~ member(ordered_pair(ordered_pair(U,V),W),flip(X))
    | member(ordered_pair(ordered_pair(V,U),W),X) ) ).

cnf(flip3,axiom,
    ( ~ member(ordered_pair(ordered_pair(V,U),W),X)
    | ~ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
    | member(ordered_pair(ordered_pair(U,V),W),flip(X)) ) ).

%----Definition of inverse.
%----a:y:(inverse(y) = domain_of(flip(cross_product(y,V)))).
cnf(inverse,axiom,
    domain_of(flip(cross_product(Y,universal_class))) = inverse(Y) ).

%----Definition of R (range_of).
%----a:z:(range_of(z) = domain_of(inverse(z))).
cnf(range_of,axiom,
    domain_of(inverse(Z)) = range_of(Z) ).

%----Definition of domain.
%----a:z:a:x:a:y:(domain(z,x,y) = first(notsub(restrict(z,x,{y}),O))).
cnf(domain,axiom,
    first(not_subclass_element(restrict(Z,X,singleton(Y)),null_class)) = domain(Z,X,Y) ).

%----Definition of range.
%----a:z:a:x:(range(z,x,y) = second(notsub(restrict(z,{x},y),O))).
cnf(range,axiom,
    second(not_subclass_element(restrict(Z,singleton(X),Y),null_class)) = range(Z,X,Y) ).

%----Definition of image.
%----a:x:a:xr:((xr image x) = range_of(restrict(xr,x,V))).
cnf(image,axiom,
    range_of(restrict(Xr,X,universal_class)) = image(Xr,X) ).

%----Definition of successor.
%----a:x:(successor(x) = (x + {x})).
cnf(successor,axiom,
    union(X,singleton(X)) = successor(X) ).

%----Explicit definition of successor_relation.
%------> ((cross_product(V,V) * ~(((E ^ ~(inverse((E + I)))) +
%----(~(E) ^ inverse((E + I)))))) = successor_relation).
%----Definition of successor_relation from the Class Existence Theorem.
%----a:x:a:y:([x,y] e successor_relation <=> x e V & successor(x) = y).
%----The above FOF does not agree with the book
cnf(successor_relation1,axiom,
    subclass(successor_relation,cross_product(universal_class,universal_class)) ).

cnf(successor_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),successor_relation)
    | successor(X) = Y ) ).

%----This is what's in the book and paper. Does not change axiom.
% input_clause(successor_relation3,axiom,
%     [--equal(successor(X),Y),
%      --member(X,universal_class),
%      ++member(ordered_pair(X,Y),successor_relation)]).

%----This is what I got by email from Quaife
cnf(successor_relation3,axiom,
    ( successor(X) != Y
    | ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | member(ordered_pair(X,Y),successor_relation) ) ).

%----Definition of inductive a:x:(inductive(x) <=> null_class
%----e x & (successor_relation image x) < x)).
cnf(inductive1,axiom,
    ( ~ inductive(X)
    | member(null_class,X) ) ).

cnf(inductive2,axiom,
    ( ~ inductive(X)
    | subclass(image(successor_relation,X),X) ) ).

cnf(inductive3,axiom,
    ( ~ member(null_class,X)
    | ~ subclass(image(successor_relation,X),X)
    | inductive(X) ) ).

%----Axiom C-1: infinity.
%----e:x:((x e V) & inductive(x) & a:y:(inductive(y) ==> (x < y))).
%----e:x:((x e V) & (O e x) & ((successor_relation image x) < x)
%----        & a:y:((O e y) & ((successor_relation image y) < y) ==>
%----(x < y))).
cnf(omega_is_inductive1,axiom,
    inductive(omega) ).

cnf(omega_is_inductive2,axiom,
    ( ~ inductive(Y)
    | subclass(omega,Y) ) ).

cnf(omega_in_universal,axiom,
    member(omega,universal_class) ).

%----These were commented out in the set Quaife sent me, and are not
%----in the paper true --> (null_class e omega).
%----true --> ((successor_relation image omega) < omega).
%----(null_class e y), ((successor_relation image y) < y) -->
%----(omega < y). true --> (omega e universal_class).

%----Definition of U (sum class).
%----a:x:(sum_class(x) = domain_of(restrict(E,V,x))).
cnf(sum_class_definition,axiom,
    domain_of(restrict(element_relation,universal_class,X)) = sum_class(X) ).

%----Axiom C-2: U (sum class).
%----a:x:((x e V) ==> (sum_class(x) e V)).
cnf(sum_class2,axiom,
    ( ~ member(X,universal_class)
    | member(sum_class(X),universal_class) ) ).

%----Definition of P (power class).
%----a:x:(power_class(x) = ~((E image ~(x)))).
cnf(power_class_definition,axiom,
    complement(image(element_relation,complement(X))) = power_class(X) ).

%----Axiom C-3: P (power class).
%----a:u:((u e V) ==> (power_class(u) e V)).
cnf(power_class2,axiom,
    ( ~ member(U,universal_class)
    | member(power_class(U),universal_class) ) ).

%----Definition of compose.
%----a:xr:a:yr:((yr ^ xr) < cross_product(V,V)).
%----a:u:a:v:a:xr:a:yr:(([u,v] e (yr ^ xr)) <=> ([u,v]
%----e cross_product(V,V)) & (v e (yr image (xr image {u})))).
%----Singleton variables OK.
cnf(compose1,axiom,
    subclass(compose(Yr,Xr),cross_product(universal_class,universal_class)) ).

cnf(compose2,axiom,
    ( ~ member(ordered_pair(Y,Z),compose(Yr,Xr))
    | member(Z,image(Yr,image(Xr,singleton(Y)))) ) ).

cnf(compose3,axiom,
    ( ~ member(Z,image(Yr,image(Xr,singleton(Y))))
    | ~ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class))
    | member(ordered_pair(Y,Z),compose(Yr,Xr)) ) ).

%----7/21/90 eliminate SINGVAL and just use FUNCTION.
%----Not eliminated in TPTP - I'm following the paper
cnf(single_valued_class1,axiom,
    ( ~ single_valued_class(X)
    | subclass(compose(X,inverse(X)),identity_relation) ) ).

cnf(single_valued_class2,axiom,
    ( ~ subclass(compose(X,inverse(X)),identity_relation)
    | single_valued_class(X) ) ).

%----Definition of function.
%----a:xf:(function(xf) <=> (xf < cross_product(V,V)) & ((xf
%----^ inverse(xf)) < identity_relation)).
cnf(function1,axiom,
    ( ~ function(Xf)
    | subclass(Xf,cross_product(universal_class,universal_class)) ) ).

cnf(function2,axiom,
    ( ~ function(Xf)
    | subclass(compose(Xf,inverse(Xf)),identity_relation) ) ).

cnf(function3,axiom,
    ( ~ subclass(Xf,cross_product(universal_class,universal_class))
    | ~ subclass(compose(Xf,inverse(Xf)),identity_relation)
    | function(Xf) ) ).

%----Axiom C-4: replacement.
%----a:x:((x e V) & function(xf) ==> ((xf image x) e V)).
cnf(replacement,axiom,
    ( ~ function(Xf)
    | ~ member(X,universal_class)
    | member(image(Xf,X),universal_class) ) ).

%----Axiom D: regularity.
%----a:x:(-(x = O) ==> e:u:((u e V) & (u e x) & ((u * x) = O))).
cnf(regularity1,axiom,
    ( X = null_class
    | member(regular(X),X) ) ).

cnf(regularity2,axiom,
    ( X = null_class
    | intersection(X,regular(X)) = null_class ) ).

%----Definition of apply (apply).
%----a:xf:a:y:((xf apply y) = sum_class((xf image {y}))).
cnf(apply,axiom,
    sum_class(image(Xf,singleton(Y))) = apply(Xf,Y) ).

%----Axiom E: universal choice.
%----e:xf:(function(xf) & a:y:((y e V) ==> (y = null_class) |
%----((xf apply y) e y))).
cnf(choice1,axiom,
    function(choice) ).

cnf(choice2,axiom,
    ( ~ member(Y,universal_class)
    | Y = null_class
    | member(apply(choice,Y),Y) ) ).

%----GROUP 2:             MORE SET THEORY DEFINITIONS.

%----Definition of one_to_one (one-to-one function).
%----a:xf:(one_to_one(xf) <=> function(xf) & function(inverse(xf))).
cnf(one_to_one1,axiom,
    ( ~ one_to_one(Xf)
    | function(Xf) ) ).

cnf(one_to_one2,axiom,
    ( ~ one_to_one(Xf)
    | function(inverse(Xf)) ) ).

cnf(one_to_one3,axiom,
    ( ~ function(inverse(Xf))
    | ~ function(Xf)
    | one_to_one(Xf) ) ).

%----Definition of S (subset relation).
cnf(subset_relation,axiom,
    intersection(cross_product(universal_class,universal_class),intersection(cross_product(universal_class,universal_class),complement(compose(complement(element_relation),inverse(element_relation))))) = subset_relation ).

%----Definition of I (identity relation).
cnf(identity_relation,axiom,
    intersection(inverse(subset_relation),subset_relation) = identity_relation ).

%----Definition of diagonalization.
%----a:xr:(diagonalise(xr) = ~(domain_of((identity_relation * xr)))).
cnf(diagonalisation,axiom,
    complement(domain_of(intersection(Xr,identity_relation))) = diagonalise(Xr) ).

%----Definition of Cantor class.
cnf(cantor_class,axiom,
    intersection(domain_of(X),diagonalise(compose(inverse(element_relation),X))) = cantor(X) ).

%----Definition of operation.
%----a:xf:(operation(xf) <=> function(xf) & (cross_product(domain_of(
%----domain_of(xf)),domain_of(domain_of(xf))) = domain_of(xf))
%----& (range_of(xf) < domain_of(domain_of(xf))).
cnf(operation1,axiom,
    ( ~ operation(Xf)
    | function(Xf) ) ).

cnf(operation2,axiom,
    ( ~ operation(Xf)
    | cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))) = domain_of(Xf) ) ).

cnf(operation3,axiom,
    ( ~ operation(Xf)
    | subclass(range_of(Xf),domain_of(domain_of(Xf))) ) ).

cnf(operation4,axiom,
    ( ~ function(Xf)
    | cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))) != domain_of(Xf)
    | ~ subclass(range_of(Xf),domain_of(domain_of(Xf)))
    | operation(Xf) ) ).

%----Definition of compatible.
%----a:xh:a:xf1:a:af2: (compatible(xh,xf1,xf2) <=> function(xh)
%----& (domain_of(domain_of(xf1)) = domain_of(xh)) & (range_of(xh)
%----< domain_of(domain_of(xf2)))).
%----Singleton variables OK.
cnf(compatible1,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | function(Xh) ) ).

%----Singleton variables OK.
cnf(compatible2,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | domain_of(domain_of(Xf1)) = domain_of(Xh) ) ).

%----Singleton variables OK.
cnf(compatible3,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | subclass(range_of(Xh),domain_of(domain_of(Xf2))) ) ).

cnf(compatible4,axiom,
    ( ~ function(Xh)
    | domain_of(domain_of(Xf1)) != domain_of(Xh)
    | ~ subclass(range_of(Xh),domain_of(domain_of(Xf2)))
    | compatible(Xh,Xf1,Xf2) ) ).

%----Definition of homomorphism.
%----a:xh:a:xf1:a:xf2: (homomorphism(xh,xf1,xf2) <=>
%---- operation(xf1) & operation(xf2) & compatible(xh,xf1,xf2) &
%---- a:x:a:y:(([x,y] e domain_of(xf1)) ==> (((xf2 apply [(xh apply x),
%----(xh apply y)]) = (xh apply (xf1 apply [x,y])))).
%----Singleton variables OK.
cnf(homomorphism1,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | operation(Xf1) ) ).

%----Singleton variables OK.
cnf(homomorphism2,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | operation(Xf2) ) ).

cnf(homomorphism3,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | compatible(Xh,Xf1,Xf2) ) ).

cnf(homomorphism4,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | ~ member(ordered_pair(X,Y),domain_of(Xf1))
    | apply(Xf2,ordered_pair(apply(Xh,X),apply(Xh,Y))) = apply(Xh,apply(Xf1,ordered_pair(X,Y))) ) ).

cnf(homomorphism5,axiom,
    ( ~ operation(Xf1)
    | ~ operation(Xf2)
    | ~ compatible(Xh,Xf1,Xf2)
    | member(ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2)),domain_of(Xf1))
    | homomorphism(Xh,Xf1,Xf2) ) ).

cnf(homomorphism6,axiom,
    ( ~ operation(Xf1)
    | ~ operation(Xf2)
    | ~ compatible(Xh,Xf1,Xf2)
    | apply(Xf2,ordered_pair(apply(Xh,not_homomorphism1(Xh,Xf1,Xf2)),apply(Xh,not_homomorphism2(Xh,Xf1,Xf2)))) != apply(Xh,apply(Xf1,ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2))))
    | homomorphism(Xh,Xf1,Xf2) ) ).

%--------------------------------------------------------------------------

```

### ./SET004-1.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET004-1 : TPTP v8.2.0. Bugfixed v1.0.1.
% Domain   : Set Theory (Boolean Algebra definitions)
% Axioms   : Set theory (Boolean algebra) axioms based on NBG set theory
% Version  : [Qua92a] axioms.
% English  :

% Refs     : [Qua92a] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [Qua92b] Quaife (1992), Email to G. Sutcliffe
% Source   : [Qua92b]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   21 (   8 unt;   0 nHn;  17 RR)
%            Number of literals    :   37 (  10 equ;  16 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :   26 (  26 usr;   7 con; 0-3 aty)
%            Number of variables   :   38 (   7 sgn)
% SPC      : 

% Comments : Requires SET004-0.ax
%          : Not all of these definitions appear in [Qua92a]. Some were
%            extracted from [Qua92b]
% Bugfixes : v1.0.1 - Duplicate axioms single_valued_term_defn? removed.
%--------------------------------------------------------------------------
%----(CO25DEF): Definition of compose_class(x) term, where x may
%----be a class. Not in [Quaife, 1992].
cnf(compose_class_definition1,axiom,
    subclass(compose_class(X),cross_product(universal_class,universal_class)) ).

cnf(compose_class_definition2,axiom,
    ( ~ member(ordered_pair(Y,Z),compose_class(X))
    | compose(X,Y) = Z ) ).

cnf(compose_class_definition3,axiom,
    ( ~ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class))
    | compose(X,Y) != Z
    | member(ordered_pair(Y,Z),compose_class(X)) ) ).

%----(CO20DEF): Definition of composition_function. Not in [Quaife,
%----1992].
cnf(definition_of_composition_function1,axiom,
    subclass(composition_function,cross_product(universal_class,cross_product(universal_class,universal_class))) ).

cnf(definition_of_composition_function2,axiom,
    ( ~ member(ordered_pair(X,ordered_pair(Y,Z)),composition_function)
    | compose(X,Y) = Z ) ).

cnf(definition_of_composition_function3,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | member(ordered_pair(X,ordered_pair(Y,compose(X,Y))),composition_function) ) ).

%----(DODEF11): Definition of domain_relation by the class existence
%----theorem. Not in [Quaife, 19992].
cnf(definition_of_domain_relation1,axiom,
    subclass(domain_relation,cross_product(universal_class,universal_class)) ).

cnf(definition_of_domain_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),domain_relation)
    | domain_of(X) = Y ) ).

cnf(definition_of_domain_relation3,axiom,
    ( ~ member(X,universal_class)
    | member(ordered_pair(X,domain_of(X)),domain_relation) ) ).

%----(SV2DEF) Definitions of terms for (SV3) Called FU2DEF in Quaife's
%----email
cnf(single_valued_term_defn1,axiom,
    first(not_subclass_element(compose(X,inverse(X)),identity_relation)) = single_valued1(X) ).

cnf(single_valued_term_defn2,axiom,
    second(not_subclass_element(compose(X,inverse(X)),identity_relation)) = single_valued2(X) ).

cnf(single_valued_term_defn3,axiom,
    domain(X,image(inverse(X),singleton(single_valued1(X))),single_valued2(X)) = single_valued3(X) ).

%----(CO14DEF): Definition of singleton relation.
cnf(compose_can_define_singleton,axiom,
    intersection(complement(compose(element_relation,complement(identity_relation))),element_relation) = singleton_relation ).

%----(AP15): definition of application function. Not in [Qua92]
cnf(application_function_defn1,axiom,
    subclass(application_function,cross_product(universal_class,cross_product(universal_class,universal_class))) ).

cnf(application_function_defn2,axiom,
    ( ~ member(ordered_pair(X,ordered_pair(Y,Z)),application_function)
    | member(Y,domain_of(X)) ) ).

cnf(application_function_defn3,axiom,
    ( ~ member(ordered_pair(X,ordered_pair(Y,Z)),application_function)
    | apply(X,Y) = Z ) ).

cnf(application_function_defn4,axiom,
    ( ~ member(ordered_pair(X,ordered_pair(Y,Z)),cross_product(universal_class,cross_product(universal_class,universal_class)))
    | ~ member(Y,domain_of(X))
    | member(ordered_pair(X,ordered_pair(Y,apply(X,Y))),application_function) ) ).

%----Definition of maps. Not in [Qua92].
%----a:xf:a:x:a:y:(maps(xf,x,y) <=> function(xf) & domain(xf)
%----= x & range(xf) < y).
cnf(maps1,axiom,
    ( ~ maps(Xf,X,Y)
    | function(Xf) ) ).

cnf(maps2,axiom,
    ( ~ maps(Xf,X,Y)
    | domain_of(Xf) = X ) ).

cnf(maps3,axiom,
    ( ~ maps(Xf,X,Y)
    | subclass(range_of(Xf),Y) ) ).

cnf(maps4,axiom,
    ( ~ function(Xf)
    | ~ subclass(range_of(Xf),Y)
    | maps(Xf,domain_of(Xf),Y) ) ).

%--------------------------------------------------------------------------

```

### ./SET005+0.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET005+0 : TPTP v8.2.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Axioms   : Set theory axioms based on NBG set theory
% Version  : [Quaife, 1992] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   43 (  16 unt;   0 def)
%            Number of atoms       :  100 (  19 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   62 (   5   ~;   3   |;  26   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   4 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 1-2 aty)
%            Number of functors    :   26 (  26 usr;   5 con; 0-3 aty)
%            Number of variables   :   86 (  81   !;   5   ?)
% SPC      : 

% Comments :
% Bugfixes : v5.4.0 - Fixed compose_defn2, added first_second, added
%            identity_relation.
%--------------------------------------------------------------------------
%----Axiom A-1: Sets are classes (omitted because all objects are
%----classes).
% input_formula(sets_are_classes,axiom,
%     ! [X] :
%       (m(X) => cls(X))).

%----Definition of subclass. By doing this early, following axioms are
%----simplified. See A-2 for a clear example. This is what Mendelson does.
fof(subclass_defn,axiom,
    ! [X,Y] :
      ( subclass(X,Y)
    <=> ! [U] :
          ( member(U,X)
         => member(U,Y) ) ) ).

%----Axiom A-2: Elements of classes are sets.
fof(class_elements_are_sets,axiom,
    ! [X] : subclass(X,universal_class) ).

%----Axiom A-3: Principle of extensionality. Quaife notes that this is
%----different from the Boyer version. It is the Mendelson version.
fof(extensionality,axiom,
    ! [X,Y] :
      ( X = Y
    <=> ( subclass(X,Y)
        & subclass(Y,X) ) ) ).

%----Axiom A-4: Existence of unordered pair
fof(unordered_pair_defn,axiom,
    ! [U,X,Y] :
      ( member(U,unordered_pair(X,Y))
    <=> ( member(U,universal_class)
        & ( U = X
          | U = Y ) ) ) ).

%----Quaife says "if I were to do it again I'd use ..."
%----McCune recommends not doing this, so I havn't
% input_formula(unordered_pair1,axiom,(
%     ! [U,X,Y] :
%       ( member(U,unordered_pair(X,Y))
%     <=> ( member(U,universal_class)
%         & ( equal(U,X)
%           | member(U,Y) ) ) )    )).

fof(unordered_pair,axiom,
    ! [X,Y] : member(unordered_pair(X,Y),universal_class) ).

%----Definition of singleton set, needed for ordered pair.
fof(singleton_set_defn,axiom,
    ! [X] : singleton(X) = unordered_pair(X,X) ).

%----Definition of ordered pair, needed for B-5
fof(ordered_pair_defn,axiom,
    ! [X,Y] : ordered_pair(X,Y) = unordered_pair(singleton(X),unordered_pair(X,singleton(Y))) ).

%----This is different from Goedel where it is
% input_formula(ordered_pair,axiom,(
%     ! [X,Y] : equal(ordered_pair(X,Y),unordered_pair(singleton(X),
% unordered_pair(X,Y)))   )).
%----This is motivated in Quaife's book p. 30 Section 3.5.

%----Axiom B-5: Cartesian product (not explicitly defined in Goedel)
%----Brought forward so cross_product can be used in B-1
%----In this and some other axioms, Goedel's axioms use existential
%----quantification rather than explicit definition.
fof(cross_product_defn,axiom,
    ! [U,V,X,Y] :
      ( member(ordered_pair(U,V),cross_product(X,Y))
    <=> ( member(U,X)
        & member(V,Y) ) ) ).

%----Added axiom to define first and second, which are introduced as Skolem
%----functions in the CNF versions of theorem OP6.
fof(first_second,axiom,
    ! [X,Y] :
      ( ( member(X,universal_class)
        & member(Y,universal_class) )
     => ( first(ordered_pair(X,Y)) = X
        & second(ordered_pair(X,Y)) = Y ) ) ).

fof(cross_product,axiom,
    ! [X,Y,Z] :
      ( member(Z,cross_product(X,Y))
     => Z = ordered_pair(first(Z),second(Z)) ) ).

%----Axiom B-1: Element relation (not explicitly defined in Goedel)
%----This is an example of undoing a simplification made by Quaife for
%----CNF systems (see book p. 28, Section 3.4).
fof(element_relation_defn,axiom,
    ! [X,Y] :
      ( member(ordered_pair(X,Y),element_relation)
    <=> ( member(Y,universal_class)
        & member(X,Y) ) ) ).

%----Quaife's version included member(X,universal_class) in the RHS of the
%----<=>, but that's not required as member(X,Y) => member(X,universal_class)
%----The equiavlence of the two forms has been proved.

fof(element_relation,axiom,
    subclass(element_relation,cross_product(universal_class,universal_class)) ).

%----Axiom B-2: Intersection (not explicitly defined in Goedel)
fof(intersection,axiom,
    ! [X,Y,Z] :
      ( member(Z,intersection(X,Y))
    <=> ( member(Z,X)
        & member(Z,Y) ) ) ).

%----Axiom B-3: Complement (not explicitly defined in Goedel)
fof(complement,axiom,
    ! [X,Z] :
      ( member(Z,complement(X))
    <=> ( member(Z,universal_class)
        & ~ member(Z,X) ) ) ).

%----Quaife has the definitions for union and symmetric difference in here
%----(about). I have moved union to later where it is needed. Symmetric
%----difference is not needed for Goedel's axioms, so I have moved it to
%----SET005+1.ax

%----Definition of restrict. Needed for B-4 domain_of
fof(restrict_defn,axiom,
    ! [X,XR,Y] : restrict(XR,X,Y) = intersection(XR,cross_product(X,Y)) ).

%----Definition of null_class. Needed for B-4 domain_of
%----This is dependent, but Plaisted says it's unreasonable to omit it.
fof(null_class_defn,axiom,
    ! [X] : ~ member(X,null_class) ).

%----Axiom B-4: Domain of (not explicitly defined in Goedel)
fof(domain_of,axiom,
    ! [X,Z] :
      ( member(Z,domain_of(X))
    <=> ( member(Z,universal_class)
        & restrict(X,singleton(Z),universal_class) != null_class ) ) ).

%----Axiom B-5 is earlier as it defines cross_product, used in B-1
%----Axiom B-6 is proved as a theorem

%----Axiom B-7: Existence of rotate (not explicitly defined in Goedel)
fof(rotate_defn,axiom,
    ! [X,U,V,W] :
      ( member(ordered_pair(ordered_pair(U,V),W),rotate(X))
    <=> ( member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
        & member(ordered_pair(ordered_pair(V,W),U),X) ) ) ).

fof(rotate,axiom,
    ! [X] : subclass(rotate(X),cross_product(cross_product(universal_class,universal_class),universal_class)) ).

%----Axiom B-8: Existence of flip (not explicitly defined in Goedel)
fof(flip_defn,axiom,
    ! [U,V,W,X] :
      ( member(ordered_pair(ordered_pair(U,V),W),flip(X))
    <=> ( member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
        & member(ordered_pair(ordered_pair(V,U),W),X) ) ) ).

fof(flip,axiom,
    ! [X] : subclass(flip(X),cross_product(cross_product(universal_class,universal_class),universal_class)) ).

%----I have removed the definitions of range and domain to SET005+1
%----as they are not needed for Goedel's axioms.

%----Plaisted's definition of union. Needed for successor
fof(union_defn,axiom,
    ! [X,Y,Z] :
      ( member(Z,union(X,Y))
    <=> ( member(Z,X)
        | member(Z,Y) ) ) ).

%----This is Quaife's original definition of union, which David Plaisted
%----suggested is unnatural ...
% input_formula(union_defn_quaife,axiom,(
%     ! [X,Y] : equal(union(X,Y),complement(intersection(complement(X),
% complement(Y))))   )).
%----Quaife's definition can be shown equivalent Plaisted's by showing each is
%----equivalent to this one ...
% input_formula(union_defn_geoff,axiom,(
%     ! [X,Y,Z] :
%       ( member(Z,union(X,Y))
%     <=> member(Z,complement(intersection(complement(X),complement(Y)))))   )).
%----as an intermediate

%----Definition of successor. Needed for successor_relation
fof(successor_defn,axiom,
    ! [X] : successor(X) = union(X,singleton(X)) ).

%----Definition of successor_relation. Needed for inductive.
fof(successor_relation_defn1,axiom,
    subclass(successor_relation,cross_product(universal_class,universal_class)) ).

%----This undoes the Quaife simplification from book p.28 Section 3.4
fof(successor_relation_defn2,axiom,
    ! [X,Y] :
      ( member(ordered_pair(X,Y),successor_relation)
    <=> ( member(X,universal_class)
        & member(Y,universal_class)
        & successor(X) = Y ) ) ).

%----Definition of inverse (not explicitly defined in Goedel)
%----Needed for range_of
fof(inverse_defn,axiom,
    ! [Y] : inverse(Y) = domain_of(flip(cross_product(Y,universal_class))) ).

%----Definition of range_of. Needed for image.
fof(range_of_defn,axiom,
    ! [Z] : range_of(Z) = domain_of(inverse(Z)) ).

%----Definition of image. Needed for inductive.
fof(image_defn,axiom,
    ! [X,XR] : image(XR,X) = range_of(restrict(XR,X,universal_class)) ).

%----Definition of inductive. Needed for C-1: Infinity
fof(inductive_defn,axiom,
    ! [X] :
      ( inductive(X)
    <=> ( member(null_class,X)
        & subclass(image(successor_relation,X),X) ) ) ).

%----Axiom C-1: Infinity
fof(infinity,axiom,
    ? [X] :
      ( member(X,universal_class)
      & inductive(X)
      & ! [Y] :
          ( inductive(Y)
         => subclass(X,Y) ) ) ).

%----Axiom C-2: Sum_class (not explicitly defined in Goedel)
fof(sum_class_defn,axiom,
    ! [U,X] :
      ( member(U,sum_class(X))
    <=> ? [Y] :
          ( member(U,Y)
          & member(Y,X) ) ) ).

%----Here is Quaife's original definition of sum_class, which David Plaisted
%----suggested is unnatural ...
%input_formula(sum_class_defn,axiom,(
%    ! [X] : equal(sum_class(X),domain_of(restrict(element_relation,
%universal_class,X)))   )).
%----Yunshan Zhu's sum class definition above has been shown equivalent to
%----the original by a longish sequence of equivalences. Boyer et al. also
%----use (a more complicated version of) the above definition.

fof(sum_class,axiom,
    ! [X] :
      ( member(X,universal_class)
     => member(sum_class(X),universal_class) ) ).

%----Axiom C-3: Existence of power_class (not explicitly defined in Goedel)
fof(power_class_defn,axiom,
    ! [U,X] :
      ( member(U,power_class(X))
    <=> ( member(U,universal_class)
        & subclass(U,X) ) ) ).

%----Here is Quaife's original definition of power_class, which David Plaisted
%----suggested is unnatural ...
%input_formula(power_class_defn,axiom,(
%    ! [X] : equal(power_class(X),complement(image(element_relation,
%complement(X))))   )).

fof(power_class,axiom,
    ! [U] :
      ( member(U,universal_class)
     => member(power_class(U),universal_class) ) ).

%----Definition of compose. Needed for function
fof(compose_defn1,axiom,
    ! [XR,YR] : subclass(compose(YR,XR),cross_product(universal_class,universal_class)) ).

%----This undoes the Quaife simplification from book p.28 Section 3.4, and
%----then simplifies that by removing a member(V,universal_class) from the RHS
fof(compose_defn2,axiom,
    ! [XR,YR,U,V] :
      ( member(ordered_pair(U,V),compose(YR,XR))
    <=> ( member(U,universal_class)
        & member(V,image(YR,image(XR,singleton(U)))) ) ) ).

%----Definition of single_valued_class. Needed for function
%----Quaife suggests not using this, in his book p.35
%input_formula(single_valued_class_defn,axiom,(
%    ! [X] :
%      ( single_valued_class(X)
%    <=> subclass(compose(X,inverse(X)),identity_relation) )   )).

%----Added definition of identity_relation (missing from Quaife)
fof(identity_relation,axiom,
    ! [Z] :
      ( member(Z,identity_relation)
    <=> ? [X] :
          ( member(X,universal_class)
          & Z = ordered_pair(X,X) ) ) ).

%----Definition of function. Needed for C-4: replacement
fof(function_defn,axiom,
    ! [XF] :
      ( function(XF)
    <=> ( subclass(XF,cross_product(universal_class,universal_class))
        & subclass(compose(XF,inverse(XF)),identity_relation) ) ) ).

%----Axiom C-4: Replacement
fof(replacement,axiom,
    ! [X,XF] :
      ( ( member(X,universal_class)
        & function(XF) )
     => member(image(XF,X),universal_class) ) ).

%----Definition of disjoint. This is omitted by Quaife
fof(disjoint_defn,axiom,
    ! [X,Y] :
      ( disjoint(X,Y)
    <=> ! [U] :
          ~ ( member(U,X)
            & member(U,Y) ) ) ).

%----Axiom D: Regularity
%----This also provides a definition of the null_class of the form
%----! [X] : ( equal(X,null_class) <= ! [U] : ~ member(U,X) )
fof(regularity,axiom,
    ! [X] :
      ( X != null_class
     => ? [U] :
          ( member(U,universal_class)
          & member(U,X)
          & disjoint(U,X) ) ) ).

%----Definition of apply. Needed for universal choice
fof(apply_defn,axiom,
    ! [XF,Y] : apply(XF,Y) = sum_class(image(XF,singleton(Y))) ).

%----Axiom E: Universal choice
fof(choice,axiom,
    ? [XF] :
      ( function(XF)
      & ! [Y] :
          ( member(Y,universal_class)
         => ( Y = null_class
            | member(apply(XF,Y),Y) ) ) ) ).

%--------------------------------------------------------------------------

```

### ./SET006+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET006+0 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Set Theory
% Axioms   : Naive set theory based on Goedel's set theory
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   11 (   1 unt;   0 def)
%            Number of atoms       :   29 (   3 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :   20 (   2   ~;   2   |;   4   &)
%                                         (  10 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    9 (   9 usr;   1 con; 0-2 aty)
%            Number of variables   :   28 (  27   !;   1   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Axioms of operations on sets
fof(subset,axiom,
    ! [A,B] :
      ( subset(A,B)
    <=> ! [X] :
          ( member(X,A)
         => member(X,B) ) ) ).

fof(equal_set,axiom,
    ! [A,B] :
      ( equal_set(A,B)
    <=> ( subset(A,B)
        & subset(B,A) ) ) ).

fof(power_set,axiom,
    ! [X,A] :
      ( member(X,power_set(A))
    <=> subset(X,A) ) ).

fof(intersection,axiom,
    ! [X,A,B] :
      ( member(X,intersection(A,B))
    <=> ( member(X,A)
        & member(X,B) ) ) ).

fof(union,axiom,
    ! [X,A,B] :
      ( member(X,union(A,B))
    <=> ( member(X,A)
        | member(X,B) ) ) ).

fof(empty_set,axiom,
    ! [X] : ~ member(X,empty_set) ).

fof(difference,axiom,
    ! [B,A,E] :
      ( member(B,difference(E,A))
    <=> ( member(B,E)
        & ~ member(B,A) ) ) ).

fof(singleton,axiom,
    ! [X,A] :
      ( member(X,singleton(A))
    <=> X = A ) ).

fof(unordered_pair,axiom,
    ! [X,A,B] :
      ( member(X,unordered_pair(A,B))
    <=> ( X = A
        | X = B ) ) ).

fof(sum,axiom,
    ! [X,A] :
      ( member(X,sum(A))
    <=> ? [Y] :
          ( member(Y,A)
          & member(X,Y) ) ) ).

fof(product,axiom,
    ! [X,A] :
      ( member(X,product(A))
    <=> ! [Y] :
          ( member(Y,A)
         => member(X,Y) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET006+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET006+1 : TPTP v8.2.0. Bugfixed v2.2.1.
% Domain   : Set Theory
% Axioms   : Mapping axioms for the SET006+0 set theory axioms
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   17 (   0 unt;   0 def)
%            Number of atoms       :   99 (   3 equ)
%            Maximal formula atoms :   11 (   5 avg)
%            Number of connectives :   82 (   0   ~;   0   |;  46   &)
%                                         (  20 <=>;  16  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   19 (  11 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  13 usr;   0 prp; 2-6 aty)
%            Number of functors    :    6 (   6 usr;   0 con; 2-5 aty)
%            Number of variables   :  105 (  97   !;   8   ?)
% SPC      : 

% Comments : Requires SET006+0.ax
% Bugfixes : v2.2.1 - compose_function and inverse_function fixed.
%------------------------------------------------------------------------------
%----Axiom and properties of mappings
fof(maps,axiom,
    ! [F,A,B] :
      ( maps(F,A,B)
    <=> ( ! [X] :
            ( member(X,A)
           => ? [Y] :
                ( member(Y,B)
                & apply(F,X,Y) ) )
        & ! [X,Y1,Y2] :
            ( ( member(X,A)
              & member(Y1,B)
              & member(Y2,B) )
           => ( ( apply(F,X,Y1)
                & apply(F,X,Y2) )
             => Y1 = Y2 ) ) ) ) ).

fof(compose_predicate,axiom,
    ! [H,G,F,A,B,C] :
      ( compose_predicate(H,G,F,A,B,C)
    <=> ! [X,Z] :
          ( ( member(X,A)
            & member(Z,C) )
         => ( apply(H,X,Z)
          <=> ? [Y] :
                ( member(Y,B)
                & apply(F,X,Y)
                & apply(G,Y,Z) ) ) ) ) ).

fof(compose_function,axiom,
    ! [G,F,A,B,C,X,Z] :
      ( ( member(X,A)
        & member(Z,C) )
     => ( apply(compose_function(G,F,A,B,C),X,Z)
      <=> ? [Y] :
            ( member(Y,B)
            & apply(F,X,Y)
            & apply(G,Y,Z) ) ) ) ).

fof(equal_maps,axiom,
    ! [F,G,A,B] :
      ( equal_maps(F,G,A,B)
    <=> ! [X,Y1,Y2] :
          ( ( member(X,A)
            & member(Y1,B)
            & member(Y2,B) )
         => ( ( apply(F,X,Y1)
              & apply(G,X,Y2) )
           => Y1 = Y2 ) ) ) ).

fof(identity,axiom,
    ! [F,A] :
      ( identity(F,A)
    <=> ! [X] :
          ( member(X,A)
         => apply(F,X,X) ) ) ).

fof(injective,axiom,
    ! [F,A,B] :
      ( injective(F,A,B)
    <=> ! [X1,X2,Y] :
          ( ( member(X1,A)
            & member(X2,A)
            & member(Y,B) )
         => ( ( apply(F,X1,Y)
              & apply(F,X2,Y) )
           => X1 = X2 ) ) ) ).

fof(surjective,axiom,
    ! [F,A,B] :
      ( surjective(F,A,B)
    <=> ! [Y] :
          ( member(Y,B)
         => ? [E] :
              ( member(E,A)
              & apply(F,E,Y) ) ) ) ).

fof(one_to_one,axiom,
    ! [F,A,B] :
      ( one_to_one(F,A,B)
    <=> ( injective(F,A,B)
        & surjective(F,A,B) ) ) ).

fof(inverse_predicate,axiom,
    ! [G,F,A,B] :
      ( inverse_predicate(G,F,A,B)
    <=> ! [X,Y] :
          ( ( member(X,A)
            & member(Y,B) )
         => ( apply(F,X,Y)
          <=> apply(G,Y,X) ) ) ) ).

fof(inverse_function,axiom,
    ! [F,A,B,X,Y] :
      ( ( member(X,A)
        & member(Y,B) )
     => ( apply(F,X,Y)
      <=> apply(inverse_function(F,A,B),Y,X) ) ) ).

fof(image2,axiom,
    ! [F,A,Y] :
      ( member(Y,image2(F,A))
    <=> ? [X] :
          ( member(X,A)
          & apply(F,X,Y) ) ) ).

fof(image3,axiom,
    ! [F,A,B,Y] :
      ( member(Y,image3(F,A,B))
    <=> ( member(Y,B)
        & ? [X] :
            ( member(X,A)
            & apply(F,X,Y) ) ) ) ).

fof(inverse_image2,axiom,
    ! [F,B,X] :
      ( member(X,inverse_image2(F,B))
    <=> ? [Y] :
          ( member(Y,B)
          & apply(F,X,Y) ) ) ).

fof(inverse_image3,axiom,
    ! [F,B,A,X] :
      ( member(X,inverse_image3(F,B,A))
    <=> ( member(X,A)
        & ? [Y] :
            ( member(Y,B)
            & apply(F,X,Y) ) ) ) ).

fof(increasing_function,axiom,
    ! [F,A,R,B,S] :
      ( increasing(F,A,R,B,S)
    <=> ! [X1,Y1,X2,Y2] :
          ( ( member(X1,A)
            & member(Y1,B)
            & member(X2,A)
            & member(Y2,B)
            & apply(R,X1,X2)
            & apply(F,X1,Y1)
            & apply(F,X2,Y2) )
         => apply(S,Y1,Y2) ) ) ).

fof(decreasing_function,axiom,
    ! [F,A,R,B,S] :
      ( decreasing(F,A,R,B,S)
    <=> ! [X1,Y1,X2,Y2] :
          ( ( member(X1,A)
            & member(Y1,B)
            & member(X2,A)
            & member(Y2,B)
            & apply(R,X1,X2)
            & apply(F,X1,Y1)
            & apply(F,X2,Y2) )
         => apply(S,Y2,Y1) ) ) ).

fof(isomorphism,axiom,
    ! [F,A,R,B,S] :
      ( isomorphism(F,A,R,B,S)
    <=> ( maps(F,A,B)
        & one_to_one(F,A,B)
        & ! [X1,Y1,X2,Y2] :
            ( ( member(X1,A)
              & member(Y1,B)
              & member(X2,A)
              & member(Y2,B)
              & apply(F,X1,Y1)
              & apply(F,X2,Y2) )
           => ( apply(R,X1,X2)
            <=> apply(S,Y1,Y2) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET006+2.ax

```vampire
%--------------------------------------------------------------------------
% File     : SET006+2 : TPTP v8.2.0. Released v2.2.0.
% Domain   : Set Theory
% Axioms   : Equivalence relation axioms for the SET006+0 set theory axioms
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   0 unt;   0 def)
%            Number of atoms       :   39 (   1 equ)
%            Maximal formula atoms :   13 (   7 avg)
%            Number of connectives :   35 (   1   ~;   0   |;  17   &)
%                                         (   5 <=>;  12  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (  10 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 2-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 3-3 aty)
%            Number of variables   :   29 (  26   !;   3   ?)
% SPC      : 

% Comments : Requires SET006+0.ax
%--------------------------------------------------------------------------
%----Equivalence relations
fof(disjoint,axiom,
    ! [A,B] :
      ( disjoint(A,B)
    <=> ~ ? [X] :
            ( member(X,A)
            & member(X,B) ) ) ).

fof(partition,axiom,
    ! [A,E] :
      ( partition(A,E)
    <=> ( ! [X] :
            ( member(X,A)
           => subset(X,E) )
        & ! [X] :
            ( member(X,E)
           => ? [Y] :
                ( member(Y,A)
                & member(X,Y) ) )
        & ! [X,Y] :
            ( ( member(X,A)
              & member(Y,A) )
           => ( ? [Z] :
                  ( member(Z,X)
                  & member(Z,Y) )
             => X = Y ) ) ) ) ).

fof(equivalence,axiom,
    ! [A,R] :
      ( equivalence(R,A)
    <=> ( ! [X] :
            ( member(X,A)
           => apply(R,X,X) )
        & ! [X,Y] :
            ( ( member(X,A)
              & member(Y,A) )
           => ( apply(R,X,Y)
             => apply(R,Y,X) ) )
        & ! [X,Y,Z] :
            ( ( member(X,A)
              & member(Y,A)
              & member(Z,A) )
           => ( ( apply(R,X,Y)
                & apply(R,Y,Z) )
             => apply(R,X,Z) ) ) ) ) ).

fof(equivalence_class,axiom,
    ! [R,E,A,X] :
      ( member(X,equivalence_class(A,E,R))
    <=> ( member(X,E)
        & apply(R,A,X) ) ) ).

fof(pre_order,axiom,
    ! [R,E] :
      ( pre_order(R,E)
    <=> ( ! [X] :
            ( member(X,E)
           => apply(R,X,X) )
        & ! [X,Y,Z] :
            ( ( member(X,E)
              & member(Y,E)
              & member(Z,E) )
           => ( ( apply(R,X,Y)
                & apply(R,Y,Z) )
             => apply(R,X,Z) ) ) ) ) ).

%--------------------------------------------------------------------------

```

### ./SET006+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET006+3 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Set Theory
% Axioms   : Order relation (Naive set theory)
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   10 (   0 unt;   0 def)
%            Number of atoms       :   56 (   3 equ)
%            Maximal formula atoms :   14 (   5 avg)
%            Number of connectives :   46 (   0   ~;   1   |;  21   &)
%                                         (  10 <=>;  14  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (   9 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   13 (  12 usr;   0 prp; 2-4 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   46 (  46   !;   0   ?)
% SPC      : 

% Comments : Requires SET006+0.ax
%------------------------------------------------------------------------------
%----Order relations
fof(order,axiom,
    ! [R,E] :
      ( order(R,E)
    <=> ( ! [X] :
            ( member(X,E)
           => apply(R,X,X) )
        & ! [X,Y] :
            ( ( member(X,E)
              & member(Y,E) )
           => ( ( apply(R,X,Y)
                & apply(R,Y,X) )
             => X = Y ) )
        & ! [X,Y,Z] :
            ( ( member(X,E)
              & member(Y,E)
              & member(Z,E) )
           => ( ( apply(R,X,Y)
                & apply(R,Y,Z) )
             => apply(R,X,Z) ) ) ) ) ).

fof(total_order,axiom,
    ! [R,E] :
      ( total_order(R,E)
    <=> ( order(R,E)
        & ! [X,Y] :
            ( ( member(X,E)
              & member(Y,E) )
           => ( apply(R,X,Y)
              | apply(R,Y,X) ) ) ) ) ).

fof(upper_bound,axiom,
    ! [R,E,M] :
      ( upper_bound(M,R,E)
    <=> ! [X] :
          ( member(X,E)
         => apply(R,X,M) ) ) ).

fof(lower_bound,axiom,
    ! [R,E,M] :
      ( lower_bound(M,R,E)
    <=> ! [X] :
          ( member(X,E)
         => apply(R,M,X) ) ) ).

fof(greatest,axiom,
    ! [R,E,M] :
      ( greatest(M,R,E)
    <=> ( member(M,E)
        & ! [X] :
            ( member(X,E)
           => apply(R,X,M) ) ) ) ).

fof(least,axiom,
    ! [R,E,M] :
      ( least(M,R,E)
    <=> ( member(M,E)
        & ! [X] :
            ( member(X,E)
           => apply(R,M,X) ) ) ) ).

fof(max,axiom,
    ! [R,E,M] :
      ( max(M,R,E)
    <=> ( member(M,E)
        & ! [X] :
            ( ( member(X,E)
              & apply(R,M,X) )
           => M = X ) ) ) ).

fof(min,axiom,
    ! [R,E,M] :
      ( min(M,R,E)
    <=> ( member(M,E)
        & ! [X] :
            ( ( member(X,E)
              & apply(R,X,M) )
           => M = X ) ) ) ).

fof(least_upper_bound,axiom,
    ! [A,X,R,E] :
      ( least_upper_bound(A,X,R,E)
    <=> ( member(A,X)
        & upper_bound(A,R,X)
        & ! [M] :
            ( ( member(M,E)
              & upper_bound(M,R,X) )
           => apply(R,A,M) ) ) ) ).

fof(greatest_lower_bound,axiom,
    ! [A,X,R,E] :
      ( greatest_lower_bound(A,X,R,E)
    <=> ( member(A,X)
        & lower_bound(A,R,X)
        & ! [M] :
            ( ( member(M,E)
              & lower_bound(M,R,X) )
           => apply(R,M,A) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET006+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET006+4 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Set Theory
% Axioms   : Ordinal numbers for the SET006+0 set theory axioms
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    8 (   0 unt;   0 def)
%            Number of atoms       :   36 (   1 equ)
%            Maximal formula atoms :   11 (   4 avg)
%            Number of connectives :   29 (   1   ~;   1   |;  12   &)
%                                         (   7 <=>;   8  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   11 (   7 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-3 aty)
%            Number of variables   :   28 (  26   !;   2   ?)
% SPC      : 

% Comments : Requires SET006+0.ax
%------------------------------------------------------------------------------
%---- Ordinal numbers and strict order relations
fof(ordinal_number,axiom,
    ! [A] :
      ( member(A,on)
    <=> ( set(A)
        & strict_well_order(member_predicate,A)
        & ! [X] :
            ( member(X,A)
           => subset(X,A) ) ) ) ).

fof(strict_well_order,axiom,
    ! [R,E] :
      ( strict_well_order(R,E)
    <=> ( strict_order(R,E)
        & ! [A] :
            ( ( subset(A,E)
              & ? [X] : member(X,A) )
           => ? [Y] : least(Y,R,A) ) ) ) ).

fof(least,axiom,
    ! [R,E,M] :
      ( least(M,R,E)
    <=> ( member(M,E)
        & ! [X] :
            ( member(X,E)
           => ( M = X
              | apply(R,M,X) ) ) ) ) ).

fof(rel_member,axiom,
    ! [X,Y] :
      ( apply(member_predicate,X,Y)
    <=> member(X,Y) ) ).

fof(strict_order,axiom,
    ! [R,E] :
      ( strict_order(R,E)
    <=> ( ! [X,Y] :
            ( ( member(X,E)
              & member(Y,E) )
           => ~ ( apply(R,X,Y)
                & apply(R,Y,X) ) )
        & ! [X,Y,Z] :
            ( ( member(X,E)
              & member(Y,E)
              & member(Z,E) )
           => ( ( apply(R,X,Y)
                & apply(R,Y,Z) )
             => apply(R,X,Z) ) ) ) ) ).

fof(set_member,axiom,
    ! [X] :
      ( set(X)
     => ! [Y] :
          ( member(Y,X)
         => set(Y) ) ) ).

fof(initial_segment,axiom,
    ! [X,R,A,Y] :
      ( member(Y,initial_segment(X,R,A))
    <=> ( member(Y,A)
        & apply(R,Y,X) ) ) ).

fof(successor,axiom,
    ! [A,X] :
      ( member(X,suc(A))
    <=> member(X,union(A,singleton(A))) ) ).

%------------------------------------------------------------------------------

```

### ./SET008^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET008^0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Set Theory
% Axioms   : Basic set theory definitions
% Version  : [Ben08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2007), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    : Typed_Set [Ben08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   28 (  14 unt;  14 typ;  14 def)
%            Number of atoms       :   35 (  18 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   36 (   5   ~;   3   |;   6   &;  21   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  21 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   70 (  70   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   16 (  14 usr;   1 con; 0-3 aty)
%            Number of variables   :   35 (  32   ^   1   !;   2   ?;  35   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
thf(in_decl,type,
    in: $i > ( $i > $o ) > $o ).

thf(in,definition,
    ( in
    = ( ^ [X: $i,M: $i > $o] : ( M @ X ) ) ) ).

thf(is_a_decl,type,
    is_a: $i > ( $i > $o ) > $o ).

thf(is_a,definition,
    ( is_a
    = ( ^ [X: $i,M: $i > $o] : ( M @ X ) ) ) ).

thf(emptyset_decl,type,
    emptyset: $i > $o ).

thf(emptyset,definition,
    ( emptyset
    = ( ^ [X: $i] : $false ) ) ).

thf(unord_pair_decl,type,
    unord_pair: $i > $i > $i > $o ).

thf(unord_pair,definition,
    ( unord_pair
    = ( ^ [X: $i,Y: $i,U: $i] :
          ( ( U = X )
          | ( U = Y ) ) ) ) ).

thf(singleton_decl,type,
    singleton: $i > $i > $o ).

thf(singleton,definition,
    ( singleton
    = ( ^ [X: $i,U: $i] : ( U = X ) ) ) ).

thf(union_decl,type,
    union: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(union,definition,
    ( union
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          | ( Y @ U ) ) ) ) ).

thf(excl_union_decl,type,
    excl_union: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(excl_union,definition,
    ( excl_union
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( ( X @ U )
            & ~ ( Y @ U ) )
          | ( ~ ( X @ U )
            & ( Y @ U ) ) ) ) ) ).

thf(intersection_decl,type,
    intersection: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(intersection,definition,
    ( intersection
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

thf(setminus_decl,type,
    setminus: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(setminus,definition,
    ( setminus
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i] :
          ( ( X @ U )
          & ~ ( Y @ U ) ) ) ) ).

thf(complement_decl,type,
    complement: ( $i > $o ) > $i > $o ).

thf(complement,definition,
    ( complement
    = ( ^ [X: $i > $o,U: $i] :
          ~ ( X @ U ) ) ) ).

thf(disjoint_decl,type,
    disjoint: ( $i > $o ) > ( $i > $o ) > $o ).

thf(disjoint,definition,
    ( disjoint
    = ( ^ [X: $i > $o,Y: $i > $o] :
          ( ( intersection @ X @ Y )
          = emptyset ) ) ) ).

thf(subset_decl,type,
    subset: ( $i > $o ) > ( $i > $o ) > $o ).

thf(subset,definition,
    ( subset
    = ( ^ [X: $i > $o,Y: $i > $o] :
        ! [U: $i] :
          ( ( X @ U )
         => ( Y @ U ) ) ) ) ).

thf(meets_decl,type,
    meets: ( $i > $o ) > ( $i > $o ) > $o ).

thf(meets,definition,
    ( meets
    = ( ^ [X: $i > $o,Y: $i > $o] :
        ? [U: $i] :
          ( ( X @ U )
          & ( Y @ U ) ) ) ) ).

thf(misses_decl,type,
    misses: ( $i > $o ) > ( $i > $o ) > $o ).

thf(misses,definition,
    ( misses
    = ( ^ [X: $i > $o,Y: $i > $o] :
          ~ ? [U: $i] :
              ( ( X @ U )
              & ( Y @ U ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET008^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET008^1 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Set Theory
% Axioms   : Definitions for functions
% Version  : [Ben08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2007), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    : Typed_Function [Ben08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   16 (   8 unt;   8 typ;   8 def)
%            Number of atoms       :   22 (  13 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   29 (   0   ~;   0   |;   3   &;  23   @)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  23 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   46 (  46   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    9 (   8 usr;   0 con; 1-3 aty)
%            Number of variables   :   26 (  16   ^   7   !;   3   ?;  26   :)
% SPC      : 

% Comments : Requires SET008^0.
%------------------------------------------------------------------------------
thf(fun_image_decl,type,
    fun_image: ( $i > $i ) > ( $i > $o ) > $i > $o ).

thf(fun_image,definition,
    ( fun_image
    = ( ^ [F: $i > $i,A: $i > $o,Y: $i] :
        ? [X: $i] :
          ( ( A @ X )
          & ( Y
            = ( F @ X ) ) ) ) ) ).

thf(fun_composition_decl,type,
    fun_composition: ( $i > $i ) > ( $i > $i ) > $i > $i ).

thf(fun_composition,definition,
    ( fun_composition
    = ( ^ [F: $i > $i,G: $i > $i,X: $i] : ( G @ ( F @ X ) ) ) ) ).

thf(fun_inv_image_decl,type,
    fun_inv_image: ( $i > $i ) > ( $i > $o ) > $i > $o ).

thf(fun_inv_image,definition,
    ( fun_inv_image
    = ( ^ [F: $i > $i,B: $i > $o,X: $i] :
        ? [Y: $i] :
          ( ( B @ Y )
          & ( Y
            = ( F @ X ) ) ) ) ) ).

thf(fun_injective_decl,type,
    fun_injective: ( $i > $i ) > $o ).

thf(fun_injective,definition,
    ( fun_injective
    = ( ^ [F: $i > $i] :
        ! [X: $i,Y: $i] :
          ( ( ( F @ X )
            = ( F @ Y ) )
         => ( X = Y ) ) ) ) ).

thf(fun_surjective_decl,type,
    fun_surjective: ( $i > $i ) > $o ).

thf(fun_surjective,definition,
    ( fun_surjective
    = ( ^ [F: $i > $i] :
        ! [Y: $i] :
        ? [X: $i] :
          ( Y
          = ( F @ X ) ) ) ) ).

thf(fun_bijective_decl,type,
    fun_bijective: ( $i > $i ) > $o ).

thf(fun_bijective,definition,
    ( fun_bijective
    = ( ^ [F: $i > $i] :
          ( ( fun_injective @ F )
          & ( fun_surjective @ F ) ) ) ) ).

thf(fun_decreasing_decl,type,
    fun_decreasing: ( $i > $i ) > ( $i > $i > $o ) > $o ).

thf(fun_decreasing,definition,
    ( fun_decreasing
    = ( ^ [F: $i > $i,SMALLER: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( SMALLER @ X @ Y )
         => ( SMALLER @ ( F @ Y ) @ ( F @ X ) ) ) ) ) ).

thf(fun_increasing_decl,type,
    fun_increasing: ( $i > $i ) > ( $i > $i > $o ) > $o ).

thf(fun_increasing,definition,
    ( fun_increasing
    = ( ^ [F: $i > $i,SMALLER: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( SMALLER @ X @ Y )
         => ( SMALLER @ ( F @ X ) @ ( F @ Y ) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET008^2.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET008^2 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Set Theory
% Axioms   : Definitions for relations
% Version  : [Ben08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2007), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    : Typed_Relation [Ben08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   42 (  21 unt;  21 typ;  21 def)
%            Number of atoms       :   51 (  25 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   88 (   3   ~;   2   |;  12   &;  62   @)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  62 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :  142 ( 142   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   22 (  21 usr;   0 con; 1-4 aty)
%            Number of variables   :   72 (  48   ^  18   !;   6   ?;  72   :)
% SPC      : 

% Comments : Requires SET008^0.
%------------------------------------------------------------------------------
thf(cartesian_product_decl,type,
    cartesian_product: ( $i > $o ) > ( $i > $o ) > $i > $i > $o ).

thf(cartesian_product,definition,
    ( cartesian_product
    = ( ^ [X: $i > $o,Y: $i > $o,U: $i,V: $i] :
          ( ( X @ U )
          & ( Y @ V ) ) ) ) ).

thf(pair_rel_decl,type,
    pair_rel: $i > $i > $i > $i > $o ).

thf(pair_rel,definition,
    ( pair_rel
    = ( ^ [X: $i,Y: $i,U: $i,V: $i] :
          ( ( U = X )
          | ( V = Y ) ) ) ) ).

thf(id_rel_decl,type,
    id_rel: ( $i > $o ) > $i > $i > $o ).

thf(id_rel,definition,
    ( id_rel
    = ( ^ [S: $i > $o,X: $i,Y: $i] :
          ( ( S @ X )
          & ( X = Y ) ) ) ) ).

thf(sub_rel_decl,type,
    sub_rel: ( $i > $i > $o ) > ( $i > $i > $o ) > $o ).

thf(sub_rel,definition,
    ( sub_rel
    = ( ^ [R1: $i > $i > $o,R2: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R1 @ X @ Y )
         => ( R2 @ X @ Y ) ) ) ) ).

thf(is_rel_on_decl,type,
    is_rel_on: ( $i > $i > $o ) > ( $i > $o ) > ( $i > $o ) > $o ).

thf(is_rel_on,definition,
    ( is_rel_on
    = ( ^ [R: $i > $i > $o,A: $i > $o,B: $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R @ X @ Y )
         => ( ( A @ X )
            & ( B @ Y ) ) ) ) ) ).

thf(restrict_rel_domain_decl,type,
    restrict_rel_domain: ( $i > $i > $o ) > ( $i > $o ) > $i > $i > $o ).

thf(restrict_rel_domain,definition,
    ( restrict_rel_domain
    = ( ^ [R: $i > $i > $o,S: $i > $o,X: $i,Y: $i] :
          ( ( S @ X )
          & ( R @ X @ Y ) ) ) ) ).

thf(rel_diagonal_decl,type,
    rel_diagonal: $i > $i > $o ).

thf(rel_diagonal,definition,
    ( rel_diagonal
    = ( ^ [X: $i,Y: $i] : ( X = Y ) ) ) ).

thf(rel_composition_decl,type,
    rel_composition: ( $i > $i > $o ) > ( $i > $i > $o ) > $i > $i > $o ).

thf(rel_composition,definition,
    ( rel_composition
    = ( ^ [R1: $i > $i > $o,R2: $i > $i > $o,X: $i,Z: $i] :
        ? [Y: $i] :
          ( ( R1 @ X @ Y )
          & ( R2 @ Y @ Z ) ) ) ) ).

thf(reflexive_decl,type,
    reflexive: ( $i > $i > $o ) > $o ).

thf(reflexive,definition,
    ( reflexive
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i] : ( R @ X @ X ) ) ) ).

thf(irreflexive_decl,type,
    irreflexive: ( $i > $i > $o ) > $o ).

thf(irreflexive,definition,
    ( irreflexive
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i] :
          ~ ( R @ X @ X ) ) ) ).

thf(symmetric_decl,type,
    symmetric: ( $i > $i > $o ) > $o ).

thf(symmetric,definition,
    ( symmetric
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R @ X @ Y )
         => ( R @ Y @ X ) ) ) ) ).

thf(transitive_decl,type,
    transitive: ( $i > $i > $o ) > $o ).

thf(transitive,definition,
    ( transitive
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i,Z: $i] :
          ( ( ( R @ X @ Y )
            & ( R @ Y @ Z ) )
         => ( R @ X @ Z ) ) ) ) ).

thf(equiv_rel__decl,type,
    equiv_rel: ( $i > $i > $o ) > $o ).

thf(equiv_rel,definition,
    ( equiv_rel
    = ( ^ [R: $i > $i > $o] :
          ( ( reflexive @ R )
          & ( symmetric @ R )
          & ( transitive @ R ) ) ) ) ).

thf(rel_codomain_decl,type,
    rel_codomain: ( $i > $i > $o ) > $i > $o ).

thf(rel_codomain,definition,
    ( rel_codomain
    = ( ^ [R: $i > $i > $o,Y: $i] :
        ? [X: $i] : ( R @ X @ Y ) ) ) ).

thf(rel_domain_decl,type,
    rel_domain: ( $i > $i > $o ) > $i > $o ).

thf(rel_domain,definition,
    ( rel_domain
    = ( ^ [R: $i > $i > $o,X: $i] :
        ? [Y: $i] : ( R @ X @ Y ) ) ) ).

thf(rel_inverse_decl,type,
    rel_inverse: ( $i > $i > $o ) > $i > $i > $o ).

thf(rel_inverse,definition,
    ( rel_inverse
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] : ( R @ Y @ X ) ) ) ).

thf(equiv_classes_decl,type,
    equiv_classes: ( $i > $i > $o ) > ( $i > $o ) > $o ).

thf(equiv_classes,definition,
    ( equiv_classes
    = ( ^ [R: $i > $i > $o,S1: $i > $o] :
        ? [X: $i] :
          ( ( S1 @ X )
          & ! [Y: $i] :
              ( ( S1 @ Y )
            <=> ( R @ X @ Y ) ) ) ) ) ).

thf(restrict_rel_codomain_decl,type,
    restrict_rel_codomain: ( $i > $i > $o ) > ( $i > $o ) > $i > $i > $o ).

thf(restrict_rel_codomain,definition,
    ( restrict_rel_codomain
    = ( ^ [R: $i > $i > $o,S: $i > $o,X: $i,Y: $i] :
          ( ( S @ Y )
          & ( R @ X @ Y ) ) ) ) ).

thf(rel_field_decl,type,
    rel_field: ( $i > $i > $o ) > $i > $o ).

thf(rel_field,definition,
    ( rel_field
    = ( ^ [R: $i > $i > $o,X: $i] :
          ( ( rel_domain @ R @ X )
          | ( rel_codomain @ R @ X ) ) ) ) ).

thf(well_founded_decl,type,
    well_founded: ( $i > $i > $o ) > $o ).

thf(well_founded,definition,
    ( well_founded
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i > $o,Z: $i] :
          ( ( X @ Z )
         => ? [Y: $i] :
              ( ( X @ Y )
              & ! [W: $i] :
                  ( ( R @ Y @ W )
                 => ~ ( X @ W ) ) ) ) ) ) ).

thf(upwards_well_founded_decl,type,
    upwards_well_founded: ( $i > $i > $o ) > $o ).

thf(upwards_well_founded,definition,
    ( upwards_well_founded
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i > $o,Z: $i] :
          ( ( X @ Z )
         => ? [Y: $i] :
              ( ( X @ Y )
              & ! [W: $i] :
                  ( ( R @ Y @ Y )
                 => ~ ( X @ W ) ) ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SET009^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SET009^0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Set Theory
% Axioms   : Binary relations
% Version  : [Nei08] axioms.
% English  : Lots of stuff about binary relations. A binary relation is just
%            anything of type $i > $i > $o. Many properties and some proofs
%            can be found in chapter 2 of [BN99].

% Refs     : [BN99]  Baader & Nipkow (1999), Term Rewriting and All That
%          : [Nei08] Neis (2008), Email to Geoff Sutcliffe
% Source   : [Nei08]
% Names    : rel.ax [Nei08]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   58 (  29 unt;  29 typ;  29 def)
%            Number of atoms       :   91 (  33 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :  158 (   4   ~;   4   |;  12   &; 122   @)
%                                         (   0 <=>;  16  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg; 122 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :  197 ( 197   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   30 (  29 usr;   0 con; 1-3 aty)
%            Number of variables   :   86 (  43   ^  38   !;   5   ?;  86   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----BASICS
%----Subrelation
thf(subrel_type,type,
    subrel: ( $i > $i > $o ) > ( $i > $i > $o ) > $o ).

thf(subrel,definition,
    ( subrel
    = ( ^ [R: $i > $i > $o,S: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R @ X @ Y )
         => ( S @ X @ Y ) ) ) ) ).

%----Inverse
thf(inv_type,type,
    inv: ( $i > $i > $o ) > $i > $i > $o ).

thf(inverse,definition,
    ( inv
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] : ( R @ Y @ X ) ) ) ).

%----IDEMPOTENCY, INFLATION, MONOTONICITY
%----Idempotency
thf(idem_type,type,
    idem: ( ( $i > $i > $o ) > $i > $i > $o ) > $o ).

thf(idempotent,definition,
    ( idem
    = ( ^ [F: ( $i > $i > $o ) > $i > $i > $o] :
        ! [R: $i > $i > $o] :
          ( ( F @ ( F @ R ) )
          = ( F @ R ) ) ) ) ).

%----Being inflationary
thf(infl_type,type,
    infl: ( ( $i > $i > $o ) > $i > $i > $o ) > $o ).

thf(inflationary,definition,
    ( infl
    = ( ^ [F: ( $i > $i > $o ) > $i > $i > $o] :
        ! [R: $i > $i > $o] : ( subrel @ R @ ( F @ R ) ) ) ) ).

%----Monotonicity
thf(mono_type,type,
    mono: ( ( $i > $i > $o ) > $i > $i > $o ) > $o ).

thf(monotonic,definition,
    ( mono
    = ( ^ [F: ( $i > $i > $o ) > $i > $i > $o] :
        ! [R: $i > $i > $o,S: $i > $i > $o] :
          ( ( subrel @ R @ S )
         => ( subrel @ ( F @ R ) @ ( F @ S ) ) ) ) ) ).

%----REFLEXIVITY, IRREFLEXIVITY, AND REFLEXIVE CLOSURE
%----Reflexivity
thf(refl_type,type,
    refl: ( $i > $i > $o ) > $o ).

thf(reflexive,definition,
    ( refl
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i] : ( R @ X @ X ) ) ) ).

%----Irreflexivity
thf(irrefl_type,type,
    irrefl: ( $i > $i > $o ) > $o ).

thf(irreflexive,definition,
    ( irrefl
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i] :
          ~ ( R @ X @ X ) ) ) ).

%----Reflexive closure
thf(rc_type,type,
    rc: ( $i > $i > $o ) > $i > $i > $o ).

thf(reflexive_closure,definition,
    ( rc
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] :
          ( ( X = Y )
          | ( R @ X @ Y ) ) ) ) ).

%----SYMMETRY, ANTISYMMETRY, ASYMMETRY, AND SYMMETRIC CLOSURE
%----Symmetry
thf(symm_type,type,
    symm: ( $i > $i > $o ) > $o ).

thf(symmetric,definition,
    ( symm
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R @ X @ Y )
         => ( R @ Y @ X ) ) ) ) ).

%----Antisymmetry
thf(antisymm_type,type,
    antisymm: ( $i > $i > $o ) > $o ).

thf(antisymmetric,definition,
    ( antisymm
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( ( R @ X @ Y )
            & ( R @ Y @ X ) )
         => ( X = Y ) ) ) ) ).

%----Asymmetry
thf(asymm_type,type,
    asymm: ( $i > $i > $o ) > $o ).

thf(asymmetric,definition,
    ( asymm
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( R @ X @ Y )
         => ~ ( R @ Y @ X ) ) ) ) ).

%----Symmetric closure
thf(sc_type,type,
    sc: ( $i > $i > $o ) > $i > $i > $o ).

thf(symmetric_closure,definition,
    ( sc
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] :
          ( ( R @ Y @ X )
          | ( R @ X @ Y ) ) ) ) ).

%----TRANSITIVITY AND TRANSITIVE CLOSURE
%----Transitivity
thf(trans_type,type,
    trans: ( $i > $i > $o ) > $o ).

thf(transitive,definition,
    ( trans
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i,Z: $i] :
          ( ( ( R @ X @ Y )
            & ( R @ Y @ Z ) )
         => ( R @ X @ Z ) ) ) ) ).

%----Transitive closure
thf(tc_type,type,
    tc: ( $i > $i > $o ) > $i > $i > $o ).

% the transitive closure of R is the smallest transitive
% relation containing R (thanks, Chad!)
thf(transitive_closure,definition,
    ( tc
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] :
        ! [S: $i > $i > $o] :
          ( ( ( trans @ S )
            & ( subrel @ R @ S ) )
         => ( S @ X @ Y ) ) ) ) ).

%----TRANSITIVE REFLEXIVE CLOSURE AND TRANSITIVE REFLEXIVE SYMMETRIC CLOSURE
%----Transitive reflexive closure
thf(trc_type,type,
    trc: ( $i > $i > $o ) > $i > $i > $o ).

thf(transitive_reflexive_closure,definition,
    ( trc
    = ( ^ [R: $i > $i > $o] : ( rc @ ( tc @ R ) ) ) ) ).

%----Transitive reflexive symmetric closure
thf(trsc_type,type,
    trsc: ( $i > $i > $o ) > $i > $i > $o ).

thf(transitive_reflexive_symmetric_closure,definition,
    ( trsc
    = ( ^ [R: $i > $i > $o] : ( sc @ ( rc @ ( tc @ R ) ) ) ) ) ).

%----ORDERS
%----Being a partial order
thf(po_type,type,
    po: ( $i > $i > $o ) > $o ).

thf(partial_order,definition,
    ( po
    = ( ^ [R: $i > $i > $o] :
          ( ( refl @ R )
          & ( antisymm @ R )
          & ( trans @ R ) ) ) ) ).

%----Being a strict (partial) order
thf(so_type,type,
    so: ( $i > $i > $o ) > $o ).

thf(strict_order,definition,
    ( so
    = ( ^ [R: $i > $i > $o] :
          ( ( asymm @ R )
          & ( trans @ R ) ) ) ) ).

%----Totality
thf(total_type,type,
    total: ( $i > $i > $o ) > $o ).

thf(total,definition,
    ( total
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( X = Y )
          | ( R @ X @ Y )
          | ( R @ Y @ X ) ) ) ) ).

%----TERMINATION AND INDUCTION
%----Termination
thf(term_type,type,
    term: ( $i > $i > $o ) > $o ).

% axiomatisation: any non-empty subset has an R-maximal element
thf(terminating,definition,
    ( term
    = ( ^ [R: $i > $i > $o] :
        ! [A: $i > $o] :
          ( ? [X: $i] : ( A @ X )
         => ? [X: $i] :
              ( ( A @ X )
              & ! [Y: $i] :
                  ( ( A @ Y )
                 => ~ ( R @ X @ Y ) ) ) ) ) ) ).

%----Satisfying the induction principle
thf(ind_type,type,
    ind: ( $i > $i > $o ) > $o ).

thf(satisfying_the_induction_principle,definition,
    ( ind
    = ( ^ [R: $i > $i > $o] :
        ! [P: $i > $o] :
          ( ! [X: $i] :
              ( ! [Y: $i] :
                  ( ( tc @ R @ X @ Y )
                 => ( P @ Y ) )
             => ( P @ X ) )
         => ! [X: $i] : ( P @ X ) ) ) ) ).

%----NORMALIZATION
%----In normal form
thf(innf_type,type,
    innf: ( $i > $i > $o ) > $i > $o ).

thf(in_normal_form,definition,
    ( innf
    = ( ^ [R: $i > $i > $o,X: $i] :
          ~ ? [Y: $i] : ( R @ X @ Y ) ) ) ).

%----Normal form of
thf(nfof_type,type,
    nfof: ( $i > $i > $o ) > $i > $i > $o ).

thf(normal_form_of,definition,
    ( nfof
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] :
          ( ( trc @ R @ Y @ X )
          & ( innf @ R @ X ) ) ) ) ).

%----Normalization
thf(norm_type,type,
    norm: ( $i > $i > $o ) > $o ).

thf(normalizing,definition,
    ( norm
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i] :
        ? [Y: $i] : ( nfof @ R @ Y @ X ) ) ) ).

%----CONFLUENCE AND FRIENDS
%----Joinability
thf(join_type,type,
    join: ( $i > $i > $o ) > $i > $i > $o ).

thf(joinable,definition,
    ( join
    = ( ^ [R: $i > $i > $o,X: $i,Y: $i] :
        ? [Z: $i] :
          ( ( trc @ R @ X @ Z )
          & ( trc @ R @ Y @ Z ) ) ) ) ).

%----Local confluence
thf(lconfl_type,type,
    lconfl: ( $i > $i > $o ) > $o ).

thf(locally_confluent,definition,
    ( lconfl
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i,Z: $i] :
          ( ( ( R @ X @ Z )
            & ( R @ X @ Y ) )
         => ( join @ R @ Z @ Y ) ) ) ) ).

%----Semi confluence
thf(sconfl_type,type,
    sconfl: ( $i > $i > $o ) > $o ).

thf(semi_confluent,definition,
    ( sconfl
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i,Z: $i] :
          ( ( ( R @ X @ Z )
            & ( trc @ R @ X @ Y ) )
         => ( join @ R @ Z @ Y ) ) ) ) ).

%----Confluence
thf(confl_type,type,
    confl: ( $i > $i > $o ) > $o ).

thf(confluent,definition,
    ( confl
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i,Z: $i] :
          ( ( ( trc @ R @ X @ Z )
            & ( trc @ R @ X @ Y ) )
         => ( join @ R @ Z @ Y ) ) ) ) ).

%----Church-Rosser property
thf(cr_type,type,
    cr: ( $i > $i > $o ) > $o ).

thf(church_rosser,definition,
    ( cr
    = ( ^ [R: $i > $i > $o] :
        ! [X: $i,Y: $i] :
          ( ( trsc @ R @ X @ Y )
         => ( join @ R @ X @ Y ) ) ) ) ).

%------------------------------------------------------------------------------

```

## Semantic Web

### ./SWB001+0.ax

Very long 3690

### ./SWB002+0.ax

Very long 806

### ./SWB003+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWB003+0 : TPTP v8.2.0. Released v5.2.0.
% Domain   : Semantic Web
% Axioms   : RDFS
% Version  : [Sch03] axioms : Especial.
% English  :

% Refs     : [Sch03] Schneider, M. (2011), Email to G. Sutcliffe
% Source   : [Sch03]
% Names    : axioms-rdfs-standard [Sch03]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   80 (  62 unt;   0 def)
%            Number of atoms       :  108 (   0 equ)
%            Maximal formula atoms :    5 (   1 avg)
%            Number of connectives :   28 (   0   ~;   0   |;   8   &)
%                                         (   5 <=>;  15  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-3 aty)
%            Number of functors    :   33 (  33 usr;  33 con; 0-0 aty)
%            Number of variables   :   37 (  37   !;   0   ?)
% SPC      : FOF_SAT_EPR

% Comments :
%------------------------------------------------------------------------------
%----I(s p o) = true -> I(p) in IP
%----Note: the "iext" predicate seems to represent a true triple,
%----not quite the IEXT mapping [CHECK!]
fof(simple_iext_property,axiom,
    ! [S,P,O] :
      ( iext(P,S,O)
     => ip(P) ) ).

%----Set IR
%----The set IR is the set of all resources.

fof(simple_ir,axiom,
    ! [X] : ir(X) ).

%----Set LV
%----The set LV of all data values is a subset of IR.
fof(simple_lv,axiom,
    ! [X] :
      ( lv(X)
     => ir(X) ) ).

%----Axiomatic Triples for the Collection Vocabulary (Lists): rdf:first
fof(rdf_collection_first_type,axiom,
    iext(uri_rdf_type,uri_rdf_first,uri_rdf_Property) ).

%----Axiomatic Triples for the Collection Vocabulary (Lists): rdf:nil
fof(rdf_collection_nil_type,axiom,
    iext(uri_rdf_type,uri_rdf_nil,uri_rdf_List) ).

%----Axiomatic Triples for the Collection Vocabulary (Lists): rdf:rest
fof(rdf_collection_rest_type,axiom,
    iext(uri_rdf_type,uri_rdf_rest,uri_rdf_Property) ).

%----Axiomatic Triples for the Container Vocabulary: rdf:_n
fof(rdf_container_n_type_001,axiom,
    iext(uri_rdf_type,uri_rdf__1,uri_rdf_Property) ).

%----Axiomatic Triples for the Container Vocabulary: rdf:_n
fof(rdf_container_n_type_002,axiom,
    iext(uri_rdf_type,uri_rdf__2,uri_rdf_Property) ).

%----Axiomatic Triples for the Container Vocabulary: rdf:_n
fof(rdf_container_n_type_003,axiom,
    iext(uri_rdf_type,uri_rdf__3,uri_rdf_Property) ).

%----Axiomatic Triples for the Reification Vocabulary: rdf:object
fof(rdf_reification_object_type,axiom,
    iext(uri_rdf_type,uri_rdf_object,uri_rdf_Property) ).

%----Axiomatic Triples for rdf:value--
fof(rdf_reification_predicate_type,axiom,
    iext(uri_rdf_type,uri_rdf_value,uri_rdf_Property) ).

%----Axiomatic Triples for the Reification Vocabulary: rdf:subject
fof(rdf_reification_subject_type,axiom,
    iext(uri_rdf_type,uri_rdf_subject,uri_rdf_Property) ).

%----IP and rdf:Property
fof(rdf_type_ip,axiom,
    ! [P] :
      ( iext(uri_rdf_type,P,uri_rdf_Property)
    <=> ip(P) ) ).

%----Axiomatic Triple for rdf:type
fof(rdf_type_type,axiom,
    iext(uri_rdf_type,uri_rdf_type,uri_rdf_Property) ).

%----Axiomatic Triple for rdf:type
fof(rdf_value_type,axiom,
    iext(uri_rdf_type,uri_rdf_type,uri_rdf_Property) ).

fof(rdfs_annotation_comment_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_comment,uri_rdfs_Resource) ).

fof(rdfs_annotation_comment_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_comment,uri_rdfs_Literal) ).

fof(rdfs_annotation_isdefinedby_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_isDefinedBy,uri_rdfs_Resource) ).

fof(rdfs_annotation_isdefinedby_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_isDefinedBy,uri_rdfs_Resource) ).

fof(rdfs_annotation_isdefinedby_sub,axiom,
    iext(uri_rdfs_subPropertyOf,uri_rdfs_isDefinedBy,uri_rdfs_seeAlso) ).

fof(rdfs_annotation_label_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_label,uri_rdfs_Resource) ).

fof(rdfs_annotation_label_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_label,uri_rdfs_Literal) ).

fof(rdfs_annotation_seealso_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_seeAlso,uri_rdfs_Resource) ).

fof(rdfs_annotation_seealso_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_seeAlso,uri_rdfs_Resource) ).

%----Definition of ICEXT
fof(rdfs_cext_def,axiom,
    ! [X,C] :
      ( iext(uri_rdf_type,X,C)
    <=> icext(C,X) ) ).

%----IC and rdfs:Resource
fof(rdfs_class_instsub_resource,axiom,
    ! [C] :
      ( ic(C)
     => iext(uri_rdfs_subClassOf,C,uri_rdfs_Resource) ) ).

%----IC and rdfs:Resource
fof(rdfs_collection_first_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_first,uri_rdf_List) ).

%----IC and rdfs:Resource
fof(rdfs_collection_first_range,axiom,
    iext(uri_rdfs_range,uri_rdf_first,uri_rdfs_Resource) ).

fof(rdfs_collection_rest_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_rest,uri_rdf_List) ).

fof(rdfs_collection_rest_range,axiom,
    iext(uri_rdfs_range,uri_rdf_rest,uri_rdf_List) ).

fof(rdfs_container_alt_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdf_Alt,uri_rdfs_Container) ).

fof(rdfs_container_bag_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdf_Bag,uri_rdfs_Container) ).

%----rdfs:ContainerMembershipProperty
fof(rdfs_container_containermembershipproperty_instsub_member,axiom,
    ! [P] :
      ( icext(uri_rdfs_ContainerMembershipProperty,P)
     => iext(uri_rdfs_subPropertyOf,P,uri_rdfs_member) ) ).

fof(rdfs_container_containermembershipproperty_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdfs_ContainerMembershipProperty,uri_rdf_Property) ).

fof(rdfs_container_member_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_member,uri_rdfs_Resource) ).

fof(rdfs_container_member_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_member,uri_rdfs_Resource) ).

fof(rdfs_container_n_domain_001,axiom,
    iext(uri_rdfs_domain,uri_rdf__1,uri_rdfs_Resource) ).

fof(rdfs_container_n_domain_002,axiom,
    iext(uri_rdfs_domain,uri_rdf__2,uri_rdfs_Resource) ).

fof(rdfs_container_n_domain_003,axiom,
    iext(uri_rdfs_domain,uri_rdf__3,uri_rdfs_Resource) ).

fof(rdfs_container_n_range_001,axiom,
    iext(uri_rdfs_range,uri_rdf__1,uri_rdfs_Resource) ).

fof(rdfs_container_n_range_002,axiom,
    iext(uri_rdfs_range,uri_rdf__2,uri_rdfs_Resource) ).

fof(rdfs_container_n_range_003,axiom,
    iext(uri_rdfs_range,uri_rdf__3,uri_rdfs_Resource) ).

fof(rdfs_container_n_type_001,axiom,
    iext(uri_rdf_type,uri_rdf__1,uri_rdfs_ContainerMembershipProperty) ).

fof(rdfs_container_n_type_002,axiom,
    iext(uri_rdf_type,uri_rdf__2,uri_rdfs_ContainerMembershipProperty) ).

fof(rdfs_container_n_type_003,axiom,
    iext(uri_rdf_type,uri_rdf__3,uri_rdfs_ContainerMembershipProperty) ).

fof(rdfs_container_seq_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdfs_Seq,uri_rdfs_Container) ).

fof(rdfs_dat_xmlliteral_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdf_XMLLiteral,uri_rdfs_Literal) ).

%----type of rdf:XMLLiteral
fof(rdfs_dat_xmlliteral_type,axiom,
    iext(uri_rdf_type,uri_rdf_XMLLiteral,uri_rdfs_Datatype) ).

%----rdfs:Datatype and rdfs:Literal
fof(rdfs_datatype_instsub_literal,axiom,
    ! [D] :
      ( icext(uri_rdfs_Datatype,D)
     => iext(uri_rdfs_subClassOf,D,uri_rdfs_Literal) ) ).

%----rdfs:Datatype is a sub class of rdfs:Class
fof(rdfs_datatype_sub,axiom,
    iext(uri_rdfs_subClassOf,uri_rdfs_Datatype,uri_rdfs_Class) ).

%----domain of rdfs:domain
fof(rdfs_domain_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_domain,uri_rdf_Property) ).

%----Semantic Condition for rdfs:domain
fof(rdfs_domain_main,axiom,
    ! [P,C,X,Y] :
      ( ( iext(uri_rdfs_domain,P,C)
        & iext(P,X,Y) )
     => icext(C,X) ) ).

%----range of rdfs:domain
fof(rdfs_domain_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_domain,uri_rdfs_Class) ).

%----Definition of set IC based on class extensions of rdfs:Class
fof(rdfs_ic_def,axiom,
    ! [X] :
      ( ic(X)
    <=> icext(uri_rdfs_Class,X) ) ).

%----Definition of set IR based on class extensions of rdfs:Resource
fof(rdfs_ir_def,axiom,
    ! [X] :
      ( ir(X)
    <=> icext(uri_rdfs_Resource,X) ) ).

%----Definition of set LV based on class extensions of rdfs:Literal
fof(rdfs_lv_def,axiom,
    ! [X] :
      ( lv(X)
    <=> icext(uri_rdfs_Literal,X) ) ).

%----type of rdf:Property (derivable RDFS-valid triple)
fof(rdfs_property_type,axiom,
    iext(uri_rdf_type,uri_rdf_Property,uri_rdfs_Class) ).

%----domain of rdfs:range
fof(rdfs_range_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_range,uri_rdf_Property) ).

%----Semantic Condition for rdfs:range
fof(rdfs_range_main,axiom,
    ! [P,C,X,Y] :
      ( ( iext(uri_rdfs_range,P,C)
        & iext(P,X,Y) )
     => icext(C,Y) ) ).

%----range of rdfs:range
fof(rdfs_range_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_range,uri_rdfs_Class) ).

fof(rdfs_reification_object_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_object,uri_rdfs_Statement) ).

fof(rdfs_reification_object_range,axiom,
    iext(uri_rdfs_range,uri_rdf_predicate,uri_rdfs_Resource) ).

fof(rdfs_reification_predicate_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_predicate,uri_rdfs_Statement) ).

fof(rdfs_reification_predicate_range,axiom,
    iext(uri_rdfs_range,uri_rdf_predicate,uri_rdfs_Resource) ).

fof(rdfs_reification_subject_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_subject,uri_rdfs_Statement) ).

fof(rdfs_reification_subject_range,axiom,
    iext(uri_rdfs_range,uri_rdf_subject,uri_rdfs_Resource) ).

%----domain of rdfs:subClassOf
fof(rdfs_subclassof_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_subClassOf,uri_rdfs_Class) ).

%----Main Semantic Conditions for rdfs:subClassOf
fof(rdfs_subclassof_main,axiom,
    ! [C,D] :
      ( iext(uri_rdfs_subClassOf,C,D)
     => ( ic(C)
        & ic(D)
        & ! [X] :
            ( icext(C,X)
           => icext(D,X) ) ) ) ).

%----range of rdfs:subClassOf
fof(rdfs_subclassof_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_subClassOf,uri_rdfs_Class) ).

%----Reflexivity of rdfs:subClassOf on IC
fof(rdfs_subclassof_reflex,axiom,
    ! [C] :
      ( ic(C)
     => iext(uri_rdfs_subClassOf,C,C) ) ).

%----Transitivity of rdfs:subClassOf on IC
fof(rdfs_subclassof_trans,axiom,
    ! [C,D,E] :
      ( ( iext(uri_rdfs_subClassOf,C,D)
        & iext(uri_rdfs_subClassOf,D,E) )
     => iext(uri_rdfs_subClassOf,C,E) ) ).

%----domain of rdfs:subPropertyOf
fof(rdfs_subpropertyof_domain,axiom,
    iext(uri_rdfs_domain,uri_rdfs_subPropertyOf,uri_rdf_Property) ).

%----Main Semantic Condition for rdfs:subPropertyOf
fof(rdfs_subpropertyof_main,axiom,
    ! [P,Q] :
      ( iext(uri_rdfs_subPropertyOf,P,Q)
     => ( ip(P)
        & ip(Q)
        & ! [X,Y] :
            ( iext(P,X,Y)
           => iext(Q,X,Y) ) ) ) ).

%----range of rdfs:subPropertyOf
fof(rdfs_subpropertyof_range,axiom,
    iext(uri_rdfs_range,uri_rdfs_subPropertyOf,uri_rdf_Property) ).

%----Reflexivity of rdfs:subPropertyOf on IP
fof(rdfs_subpropertyof_reflex,axiom,
    ! [P] :
      ( ip(P)
     => iext(uri_rdfs_subPropertyOf,P,P) ) ).

%----Transitivity of rdfs:subPropertyOf on IP
fof(rdfs_subpropertyof_trans,axiom,
    ! [P,Q,R] :
      ( ( iext(uri_rdfs_subPropertyOf,P,Q)
        & iext(uri_rdfs_subPropertyOf,Q,R) )
     => iext(uri_rdfs_subPropertyOf,P,R) ) ).

%----domain of rdf:type
fof(rdfs_type_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_type,uri_rdfs_Resource) ).

%----range of rdf:type
fof(rdfs_type_range,axiom,
    iext(uri_rdfs_range,uri_rdf_type,uri_rdfs_Class) ).

fof(rdfs_value_domain,axiom,
    iext(uri_rdfs_domain,uri_rdf_value,uri_rdfs_Resource) ).

fof(rdfs_value_range,axiom,
    iext(uri_rdfs_range,uri_rdf_value,uri_rdfs_Resource) ).

%------------------------------------------------------------------------------

```

### ./SWB003+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWB003+1 : TPTP v8.2.0. Released v5.2.0.
% Domain   : Semantic Web
% Axioms   : RDFS Extensional axioms
% Version  : [Sch03] axioms : Especial.
% English  :

% Refs     : [Sch03] Schneider, M. (2011), Email to G. Sutcliffe
% Source   : [Sch03]
% Names    : axioms-rdfsext-standard [Sch03]

% Status   : Satisfiable
% Syntax   : Number of formulae    :    4 (   0 unt;   0 def)
%            Number of atoms       :   20 (   0 equ)
%            Maximal formula atoms :    5 (   5 avg)
%            Number of connectives :   16 (   0   ~;   0   |;   8   &)
%                                         (   4 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   9 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :    4 (   4 usr;   4 con; 0-0 aty)
%            Number of variables   :   15 (  15   !;   0   ?)
% SPC      : FOF_SAT_RFO_NEQ

% Comments : Requires SWB003+0.ax
%------------------------------------------------------------------------------
%----rdfs:domain
fof(owl_rdfsext_domain,axiom,
    ! [P,C] :
      ( iext(uri_rdfs_domain,P,C)
    <=> ( ip(P)
        & ic(C)
        & ! [X,Y] :
            ( iext(P,X,Y)
           => icext(C,X) ) ) ) ).

%----rdfs:range
fof(owl_rdfsext_range,axiom,
    ! [P,C] :
      ( iext(uri_rdfs_range,P,C)
    <=> ( ip(P)
        & ip(C)
        & ! [X,Y] :
            ( iext(P,X,Y)
           => icext(C,Y) ) ) ) ).

%----rdfs:subClassOf
fof(owl_rdfsext_subclassof,axiom,
    ! [C1,C2] :
      ( iext(uri_rdfs_subClassOf,C1,C2)
    <=> ( ic(C1)
        & ic(C2)
        & ! [X] :
            ( icext(C1,X)
           => icext(C2,X) ) ) ) ).

%----rdfs:subPropertyOf
fof(owl_rdfsext_subpropertyof,axiom,
    ! [P1,P2] :
      ( iext(uri_rdfs_subPropertyOf,P1,P2)
    <=> ( ip(P1)
        & ip(P2)
        & ! [X,Y] :
            ( iext(P1,X,Y)
           => iext(P2,X,Y) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWC001+0.ax

Very long 815

### ./SWC001-0.ax

Very long 999

### ./SWV001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : SWV001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Software Verification
% Axioms   : Program verification axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   12 (   5 unt;   1 nHn;   7 RR)
%            Number of literals    :   23 (   9 equ;  11 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   0 con; 1-1 aty)
%            Number of variables   :   22 (   0 sgn)
% SPC      : 

% Comments : Only reflexivity is specified from equality, i.e. no symmetry
%            or transitivity.
%          : These axioms were contributed to [MOW76] in private
%            correspondance from G. Ernst.
%--------------------------------------------------------------------------
cnf(predecessor_successor,axiom,
    predecessor(successor(X)) = X ).

cnf(successor_predecessor,axiom,
    successor(predecessor(X)) = X ).

cnf(well_defined_predecessor,axiom,
    ( X = Y
    | predecessor(X) != predecessor(Y) ) ).

cnf(well_defined_successor,axiom,
    ( X = Y
    | successor(X) != successor(Y) ) ).

cnf(predecessor_less_than,axiom,
    less_than(predecessor(X),X) ).

cnf(less_than_successor,axiom,
    less_than(X,successor(X)) ).

cnf(transitivity_of_less_than,axiom,
    ( less_than(X,Z)
    | ~ less_than(X,Y)
    | ~ less_than(Y,Z) ) ).

cnf(all_related,axiom,
    ( less_than(X,Y)
    | less_than(Y,X)
    | X = Y ) ).

cnf(x_not_less_than_x,axiom,
    ~ less_than(X,X) ).

cnf(anti_symmetry_of_less_than,axiom,
    ( ~ less_than(X,Y)
    | ~ less_than(Y,X) ) ).

cnf(equal_and_less_than_transitivity1,axiom,
    ( less_than(Y,Z)
    | X != Y
    | ~ less_than(X,Z) ) ).

cnf(equal_and_less_than_transitivity2,axiom,
    ( less_than(Z,Y)
    | X != Y
    | ~ less_than(Z,X) ) ).

%--------------------------------------------------------------------------

```

### ./SWV002-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : SWV002-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Software Verification
% Axioms   : Program verification axioms
% Version  : [MOW76] axioms.
% English  : These "clauses arose in a natural manner from work done
%            in program verification" [MOW76] p.779.

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :   22 (   6 unt;   2 nHn;  19 RR)
%            Number of literals    :   52 (   3 equ;  30 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   11 (  10 usr;   0 prp; 1-4 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   48 (   5 sgn)
% SPC      : 

% Comments : These axioms were contributed to [MOW76] by E. McCharen. The
%            axioms are incomplete.
%          : Due to clause_2 being incomplete, no problems have been defined
%            on these axioms.
%--------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ q1(Vj,Vt,Vx)
    | q2(Vj,e(Vx,n1),Vx) ) ).

%----The second literal is not printed in [MOW76].
%----So this literal may be wrong
cnf(clause_2,axiom,
    ( ~ q2(Vj,Vt,Vx)
    | q3(successor(n1),Vt,VWhat) ) ).

cnf(clause_3,axiom,
    ( ~ q3(Vj,Vt,Vx)
    | ~ less_or_equal(Vj,n)
    | q4(Vj,Vt,Vx) ) ).

cnf(clause_4,axiom,
    ( ~ q3(Vj,Vt,Vx)
    | less_or_equal(Vj,n)
    | q7(Vj,Vt,Vx) ) ).

cnf(clause_5,axiom,
    ( ~ q4(Vj,Vt,Vx)
    | ~ d(Vj)
    | ~ less_or_equal(e(Vx,Vj),Vt)
    | q6(Vj,Vt,Vx) ) ).

cnf(clause_6,axiom,
    ( ~ q4(Vj,Vt,Vx)
    | ~ d(Vj)
    | less_or_equal(e(Vx,Vj),Vt)
    | q5(Vj,Vt,Vx) ) ).

cnf(clause_7,axiom,
    ( ~ q5(Vj,Vt,Vx)
    | ~ d(Vj)
    | q6(Vj,e(Vx,Vj),Vx) ) ).

cnf(clause_8,axiom,
    ( ~ q6(Vj,Vt,Vx)
    | q3(successor(Vj),Vt,Vx) ) ).

cnf(definition_of_d_1,axiom,
    ( ~ less_or_equal(n1,X)
    | ~ less_or_equal(X,n)
    | d(X) ) ).

cnf(definition_of_d_2,axiom,
    ( ~ d(X)
    | ~ less_or_equal(n1,X) ) ).

cnf(definition_of_d_3,axiom,
    ( ~ d(X)
    | less_or_equal(X,n) ) ).

cnf(one_is_d,axiom,
    d(n1) ).

cnf(n_is_d,axiom,
    d(n) ).

cnf(clause_9,axiom,
    less_or_equal(n1,n) ).

cnf(clause_10,axiom,
    ( ~ ub(W1,X,Y,Z)
    | ~ less_or_equal(W1,W2)
    | ub(W2,X,Y,Z) ) ).

cnf(clause_11,axiom,
    ( ~ ub(W,X,Y,Z1)
    | successor(Z1) != Z2
    | ~ d(Z2)
    | ~ less_or_equal(e(X,Z2),W)
    | ub(W,X,Y,Z2) ) ).

cnf(successor_not_less_or_equal,axiom,
    ~ less_or_equal(successor(X),X) ).

cnf(less_or_equal_than_successor,axiom,
    less_or_equal(X,successor(X)) ).

cnf(less_or_equal_reflexivity,axiom,
    less_or_equal(X,X) ).

cnf(less_or_equal_implies_equal,axiom,
    ( ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,X)
    | X = Y ) ).

cnf(transitivity_of_less_or_equal,axiom,
    ( ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,Z)
    | less_or_equal(X,Z) ) ).

cnf(equal_implies_less_or_equal,axiom,
    ( less_or_equal(X,Y)
    | X != Y ) ).

%--------------------------------------------------------------------------

```

### ./SWV003+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV003+0 : TPTP v8.2.0. Bugfixed v3.3.0.
% Domain   : Software Verification
% Axioms   : NASA software certification axioms
% Version  : [DFS04] axioms : Especial.
% English  :

% Refs     : [Fis04] Fischer (2004), Email to G. Sutcliffe
%          : [DFS04] Denney et al. (2004), Using Automated Theorem Provers
% Source   : [Fis04]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   52 (  23 unt;   0 def)
%            Number of atoms       :  190 (  54 equ)
%            Maximal formula atoms :   20 (   3 avg)
%            Number of connectives :  143 (   5   ~;   2   |;  86   &)
%                                         (   5 <=>;  45  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   18 (   5 avg)
%            Maximal term depth    :    9 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   1 prp; 0-2 aty)
%            Number of functors    :   28 (  28 usr;  10 con; 0-4 aty)
%            Number of variables   :  162 ( 162   !;   0   ?)
% SPC      : 

% Comments :
% Bugfixes : v3.3.0 - Fixed symmetry axioms
%------------------------------------------------------------------------------
%----Axioms for gt
fof(totality,axiom,
    ! [X,Y] :
      ( gt(X,Y)
      | gt(Y,X)
      | X = Y ) ).

fof(transitivity_gt,axiom,
    ! [X,Y,Z] :
      ( ( gt(X,Y)
        & gt(Y,Z) )
     => gt(X,Z) ) ).

fof(irreflexivity_gt,axiom,
    ! [X] : ~ gt(X,X) ).

%----Axioms for leq
fof(reflexivity_leq,axiom,
    ! [X] : leq(X,X) ).

fof(transitivity_leq,axiom,
    ! [X,Y,Z] :
      ( ( leq(X,Y)
        & leq(Y,Z) )
     => leq(X,Z) ) ).

%----Axioms for lt/geq
fof(lt_gt,axiom,
    ! [X,Y] :
      ( lt(X,Y)
    <=> gt(Y,X) ) ).

fof(leq_geq,axiom,
    ! [X,Y] :
      ( geq(X,Y)
    <=> leq(Y,X) ) ).

%----Axioms for combinations of gt and leq
fof(leq_gt1,axiom,
    ! [X,Y] :
      ( gt(Y,X)
     => leq(X,Y) ) ).

fof(leq_gt2,axiom,
    ! [X,Y] :
      ( ( leq(X,Y)
        & X != Y )
     => gt(Y,X) ) ).

%----leq/gt and pred/succ
fof(leq_gt_pred,axiom,
    ! [X,Y] :
      ( leq(X,pred(Y))
    <=> gt(Y,X) ) ).

fof(gt_succ,axiom,
    ! [X] : gt(succ(X),X) ).

fof(leq_succ,axiom,
    ! [X,Y] :
      ( leq(X,Y)
     => leq(X,succ(Y)) ) ).

fof(leq_succ_gt_equiv,axiom,
    ! [X,Y] :
      ( leq(X,Y)
    <=> gt(succ(Y),X) ) ).

%----uniform_int_rand
%----Restriction:  LB of uniform_int_rnd is 0
fof(uniform_int_rand_ranges_hi,axiom,
    ! [X,C] :
      ( leq(n0,X)
     => leq(uniform_int_rnd(C,X),X) ) ).

fof(uniform_int_rand_ranges_lo,axiom,
    ! [X,C] :
      ( leq(n0,X)
     => leq(n0,uniform_int_rnd(C,X)) ) ).

%----Axioms for constant arrays
fof(const_array1_select,axiom,
    ! [I,L,U,Val] :
      ( ( leq(L,I)
        & leq(I,U) )
     => a_select2(tptp_const_array1(dim(L,U),Val),I) = Val ) ).

fof(const_array2_select,axiom,
    ! [I,L1,U1,J,L2,U2,Val] :
      ( ( leq(L1,I)
        & leq(I,U1)
        & leq(L2,J)
        & leq(J,U2) )
     => a_select3(tptp_const_array2(dim(L1,U1),dim(L2,U2),Val),I,J) = Val ) ).

%----Symmetry axioms for matrix operations
fof(matrix_symm_trans,axiom,
    ! [A,N] :
      ( ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(A,I,J) = a_select3(A,J,I) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(trans(A),I,J) = a_select3(trans(A),J,I) ) ) ).

fof(matrix_symm_inv,axiom,
    ! [A,N] :
      ( ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(A,I,J) = a_select3(A,J,I) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(inv(A),I,J) = a_select3(inv(A),J,I) ) ) ).

fof(matrix_symm_update_diagonal,axiom,
    ! [A,N] :
      ( ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(A,I,J) = a_select3(A,J,I) )
     => ! [I,J,K,VAL] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N)
            & leq(n0,K)
            & leq(K,N) )
         => a_select3(tptp_update3(A,K,K,VAL),I,J) = a_select3(tptp_update3(A,K,K,VAL),J,I) ) ) ).

fof(matrix_symm_add,axiom,
    ! [A,B,N] :
      ( ( ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(A,I,J) = a_select3(A,J,I) )
        & ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(B,I,J) = a_select3(B,J,I) ) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(tptp_madd(A,B),I,J) = a_select3(tptp_madd(A,B),J,I) ) ) ).

fof(matrix_symm_sub,axiom,
    ! [A,B,N] :
      ( ( ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(A,I,J) = a_select3(A,J,I) )
        & ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(B,I,J) = a_select3(B,J,I) ) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(tptp_msub(A,B),I,J) = a_select3(tptp_msub(A,B),J,I) ) ) ).

fof(matrix_symm_aba1,axiom,
    ! [A,B,N] :
      ( ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(B,I,J) = a_select3(B,J,I) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(tptp_mmul(A,tptp_mmul(B,trans(A))),I,J) = a_select3(tptp_mmul(A,tptp_mmul(B,trans(A))),J,I) ) ) ).

%----This is the generalized version where the matrix dimensions
%----can be different for B and the ABA'
fof(matrix_symm_aba2,axiom,
    ! [A,B,N,M] :
      ( ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,M)
            & leq(n0,J)
            & leq(J,M) )
         => a_select3(B,I,J) = a_select3(B,J,I) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(tptp_mmul(A,tptp_mmul(B,trans(A))),I,J) = a_select3(tptp_mmul(A,tptp_mmul(B,trans(A))),J,I) ) ) ).

fof(matrix_symm_joseph_update,axiom,
    ! [A,B,C,D,E,F,N,M] :
      ( ( ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,M)
              & leq(n0,J)
              & leq(J,M) )
           => a_select3(D,I,J) = a_select3(D,J,I) )
        & ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(A,I,J) = a_select3(A,J,I) )
        & ! [I,J] :
            ( ( leq(n0,I)
              & leq(I,N)
              & leq(n0,J)
              & leq(J,N) )
           => a_select3(F,I,J) = a_select3(F,J,I) ) )
     => ! [I,J] :
          ( ( leq(n0,I)
            & leq(I,N)
            & leq(n0,J)
            & leq(J,N) )
         => a_select3(tptp_madd(A,tptp_mmul(B,tptp_mmul(tptp_madd(tptp_mmul(C,tptp_mmul(D,trans(C))),tptp_mmul(E,tptp_mmul(F,trans(E)))),trans(B)))),I,J) = a_select3(tptp_madd(A,tptp_mmul(B,tptp_mmul(tptp_madd(tptp_mmul(C,tptp_mmul(D,trans(C))),tptp_mmul(E,tptp_mmul(F,trans(E)))),trans(B)))),J,I) ) ) ).

%----handling of sums
fof(sum_plus_base,axiom,
    ! [Body] : sum(n0,tptp_minus_1,Body) = n0 ).

fof(sum_plus_base_float,axiom,
    ! [Body] : tptp_float_0_0 = sum(n0,tptp_minus_1,Body) ).

%----AXIOMS NECESSARY FOR UNSIMPLIFIED TASKS

%----successor/predecessor
fof(succ_tptp_minus_1,axiom,
    succ(tptp_minus_1) = n0 ).

fof(succ_plus_1_r,axiom,
    ! [X] : plus(X,n1) = succ(X) ).

fof(succ_plus_1_l,axiom,
    ! [X] : plus(n1,X) = succ(X) ).

fof(succ_plus_2_r,axiom,
    ! [X] : plus(X,n2) = succ(succ(X)) ).

fof(succ_plus_2_l,axiom,
    ! [X] : plus(n2,X) = succ(succ(X)) ).

fof(succ_plus_3_r,axiom,
    ! [X] : plus(X,n3) = succ(succ(succ(X))) ).

fof(succ_plus_3_l,axiom,
    ! [X] : plus(n3,X) = succ(succ(succ(X))) ).

fof(succ_plus_4_r,axiom,
    ! [X] : plus(X,n4) = succ(succ(succ(succ(X)))) ).

fof(succ_plus_4_l,axiom,
    ! [X] : plus(n4,X) = succ(succ(succ(succ(X)))) ).

fof(succ_plus_5_r,axiom,
    ! [X] : plus(X,n5) = succ(succ(succ(succ(succ(X))))) ).

fof(succ_plus_5_l,axiom,
    ! [X] : plus(n5,X) = succ(succ(succ(succ(succ(X))))) ).

fof(pred_minus_1,axiom,
    ! [X] : minus(X,n1) = pred(X) ).

fof(pred_succ,axiom,
    ! [X] : pred(succ(X)) = X ).

fof(succ_pred,axiom,
    ! [X] : succ(pred(X)) = X ).

%----leq/gt and successor
fof(leq_succ_succ,axiom,
    ! [X,Y] :
      ( leq(succ(X),succ(Y))
    <=> leq(X,Y) ) ).

fof(leq_succ_gt,axiom,
    ! [X,Y] :
      ( leq(succ(X),Y)
     => gt(Y,X) ) ).

%----leq/gt and plus/minus
fof(leq_minus,axiom,
    ! [X,Y] :
      ( leq(minus(X,Y),X)
     => leq(n0,Y) ) ).

%----select_update
fof(sel3_update_1,axiom,
    ! [X,U,V,VAL] : a_select3(tptp_update3(X,U,V,VAL),U,V) = VAL ).

fof(sel3_update_2,axiom,
    ! [I,J,U,V,X,VAL,VAL2] :
      ( ( I != U
        & J = V
        & a_select3(X,U,V) = VAL )
     => a_select3(tptp_update3(X,I,J,VAL2),U,V) = VAL ) ).

fof(sel3_update_3,axiom,
    ! [I,J,U,V,X,VAL] :
      ( ( ! [I0,J0] :
            ( ( leq(n0,I0)
              & leq(n0,J0)
              & leq(I0,U)
              & leq(J0,V) )
           => a_select3(X,I0,J0) = VAL )
        & leq(n0,I)
        & leq(I,U)
        & leq(n0,J)
        & leq(J,V) )
     => a_select3(tptp_update3(X,U,V,VAL),I,J) = VAL ) ).

fof(sel2_update_1,axiom,
    ! [X,U,VAL] : a_select2(tptp_update2(X,U,VAL),U) = VAL ).

fof(sel2_update_2,axiom,
    ! [I,U,X,VAL,VAL2] :
      ( ( I != U
        & a_select2(X,U) = VAL )
     => a_select2(tptp_update2(X,I,VAL2),U) = VAL ) ).

fof(sel2_update_3,axiom,
    ! [I,U,X,VAL] :
      ( ( ! [I0] :
            ( ( leq(n0,I0)
              & leq(I0,U) )
           => a_select2(X,I0) = VAL )
        & leq(n0,I)
        & leq(I,U) )
     => a_select2(tptp_update2(X,U,VAL),I) = VAL ) ).

%----True
fof(ttrue,axiom,
    true ).

%----def and use inequality
fof(defuse,axiom,
    def != use ).

```

### ./SWV004-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV004-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for messages
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Message.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   40 (   9 unt;   6 nHn;  38 RR)
%            Number of literals    :   80 (  26 equ;  41 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   17 (  17 usr;   4 con; 0-3 aty)
%            Number of variables   :   91 (  21 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax
%------------------------------------------------------------------------------
cnf(cls_Message_OCrypt__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OHash__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_n),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_n),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_Oagent_Odistinct__1__iff1_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OFriend(V_nat_H) ).

cnf(cls_Message_Oagent_Odistinct__2__iff1_0,axiom,
    c_Message_Oagent_OFriend(V_nat_H) != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__3__iff1_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__4__iff1_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__5__iff1_0,axiom,
    c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__6__iff1_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OFriend(V_nat) ).

cnf(cls_Message_Oagent_Oinject__iff1_0,axiom,
    ( c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OFriend(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__analzD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oanalz(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oin__parts__UnE_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_union(V_G,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_G),tc_Message_Omsg) ) ).

cnf(cls_Message_Omsg_Oinject__1__iff1_0,axiom,
    ( c_Message_Omsg_OAgent(V_agent) != c_Message_Omsg_OAgent(V_agent_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Message_Omsg_Oinject__2__iff1_0,axiom,
    ( c_Message_Omsg_ONumber(V_nat) != c_Message_Omsg_ONumber(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__3__iff1_0,axiom,
    ( c_Message_Omsg_ONonce(V_nat) != c_Message_Omsg_ONonce(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__4__iff1_0,axiom,
    ( c_Message_Omsg_OKey(V_nat) != c_Message_Omsg_OKey(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__5__iff1_0,axiom,
    ( c_Message_Omsg_OHash(V_msg) != c_Message_Omsg_OHash(V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Omsg_Oinject__6__iff1_0,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg1 = V_msg1_H ) ).

cnf(cls_Message_Omsg_Oinject__6__iff1_1,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg2 = V_msg2_H ) ).

cnf(cls_Message_Omsg_Oinject__7__iff1_0,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__7__iff1_1,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Oparts_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__emptyE_0,axiom,
    ~ c_in(V_X,c_Message_Oparts(c_emptyset),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__partsD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(c_Message_Oparts(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OAgent_0,axiom,
    c_in(c_Message_Omsg_OAgent(V_agt),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Osynth_OCrypt_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OHash_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OMPair_0,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_ONumber_0,axiom,
    c_in(c_Message_Omsg_ONumber(V_n),c_Message_Osynth(V_H),tc_Message_Omsg) ).

%------------------------------------------------------------------------------

```

### ./SWV005-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for messages
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Message-simp.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   44 (  30 unt;   0 nHn;  25 RR)
%            Number of literals    :   58 (  51 equ;  21 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   23 (  23 usr;   7 con; 0-3 aty)
%            Number of variables   :   77 (  29 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax
%------------------------------------------------------------------------------
cnf(cls_Message_OMPair__parts_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oagent_Odistinct__1_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OFriend(V_nat_H) ).

cnf(cls_Message_Oagent_Odistinct__2_0,axiom,
    c_Message_Oagent_OFriend(V_nat_H) != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__3_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__4_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__5_0,axiom,
    c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__6_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OFriend(V_nat) ).

cnf(cls_Message_Oagent_Oinject_0,axiom,
    ( c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OFriend(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Oagent_Osize__1_0,axiom,
    c_Nat_Osize(c_Message_Oagent_OServer,tc_Message_Oagent) = c_0 ).

cnf(cls_Message_Oagent_Osize__2_0,axiom,
    c_Nat_Osize(c_Message_Oagent_OFriend(V_nat),tc_Message_Oagent) = c_0 ).

cnf(cls_Message_Oagent_Osize__3_0,axiom,
    c_Nat_Osize(c_Message_Oagent_OSpy,tc_Message_Oagent) = c_0 ).

cnf(cls_Message_OinvKey_A_IinvKey_Ay_J_A_61_61_Ay_0,axiom,
    c_Message_OinvKey(c_Message_OinvKey(V_y)) = V_y ).

cnf(cls_Message_OinvKey__eq_0,axiom,
    ( c_Message_OinvKey(V_K) != c_Message_OinvKey(V_K_H)
    | V_K = V_K_H ) ).

cnf(cls_Message_OkeysFor__Un_0,axiom,
    c_Message_OkeysFor(c_union(V_H,V_H_H,tc_Message_Omsg)) = c_union(c_Message_OkeysFor(V_H),c_Message_OkeysFor(V_H_H),tc_nat) ).

cnf(cls_Message_OkeysFor__empty_0,axiom,
    c_Message_OkeysFor(c_emptyset) = c_emptyset ).

cnf(cls_Message_OkeysFor__insert__Agent_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_OAgent(V_A),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_OkeysFor__insert__Crypt_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_OinvKey(V_K),c_Message_OkeysFor(V_H),tc_nat) ).

cnf(cls_Message_OkeysFor__insert__Hash_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_OkeysFor__insert__Key_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_OkeysFor__insert__MPair_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_OkeysFor__insert__Nonce_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_OkeysFor__insert__Number_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_Omsg_ONumber(V_N),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_Omsg_Oinject__1_0,axiom,
    ( c_Message_Omsg_OAgent(V_agent) != c_Message_Omsg_OAgent(V_agent_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Message_Omsg_Oinject__2_0,axiom,
    ( c_Message_Omsg_ONumber(V_nat) != c_Message_Omsg_ONumber(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__3_0,axiom,
    ( c_Message_Omsg_ONonce(V_nat) != c_Message_Omsg_ONonce(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__4_0,axiom,
    ( c_Message_Omsg_OKey(V_nat) != c_Message_Omsg_OKey(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__5_0,axiom,
    ( c_Message_Omsg_OHash(V_msg) != c_Message_Omsg_OHash(V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Omsg_Oinject__6_0,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg1 = V_msg1_H ) ).

cnf(cls_Message_Omsg_Oinject__6_1,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg2 = V_msg2_H ) ).

cnf(cls_Message_Omsg_Oinject__7_0,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__7_1,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Omsg_Osize__1_0,axiom,
    c_Nat_Osize(c_Message_Omsg_OAgent(V_agent),tc_Message_Omsg) = c_0 ).

cnf(cls_Message_Omsg_Osize__2_0,axiom,
    c_Nat_Osize(c_Message_Omsg_ONumber(V_nat),tc_Message_Omsg) = c_0 ).

cnf(cls_Message_Omsg_Osize__3_0,axiom,
    c_Nat_Osize(c_Message_Omsg_ONonce(V_nat),tc_Message_Omsg) = c_0 ).

cnf(cls_Message_Omsg_Osize__4_0,axiom,
    c_Nat_Osize(c_Message_Omsg_OKey(V_nat),tc_Message_Omsg) = c_0 ).

cnf(cls_Message_Omsg_Osize__5_0,axiom,
    c_Nat_Osize(c_Message_Omsg_OHash(V_msg),tc_Message_Omsg) = c_plus(c_Nat_Osize(V_msg,tc_Message_Omsg),c_Suc(c_0),tc_nat) ).

cnf(cls_Message_Omsg_Osize__6_0,axiom,
    c_Nat_Osize(c_Message_Omsg_OMPair(V_msg1,V_msg2),tc_Message_Omsg) = c_plus(c_plus(c_Nat_Osize(V_msg1,tc_Message_Omsg),c_Nat_Osize(V_msg2,tc_Message_Omsg),tc_nat),c_Suc(c_0),tc_nat) ).

cnf(cls_Message_Omsg_Osize__7_0,axiom,
    c_Nat_Osize(c_Message_Omsg_OCrypt(V_nat,V_msg),tc_Message_Omsg) = c_plus(c_Nat_Osize(V_msg,tc_Message_Omsg),c_Suc(c_0),tc_nat) ).

cnf(cls_Message_Oparts_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__Un_0,axiom,
    c_Message_Oparts(c_union(V_G,V_H,tc_Message_Omsg)) = c_union(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__emptyE_0,axiom,
    ~ c_in(V_X,c_Message_Oparts(c_emptyset),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__empty_0,axiom,
    c_Message_Oparts(c_emptyset) = c_emptyset ).

cnf(cls_Message_Ostrange__Un__eq_0,axiom,
    c_union(V_A,c_union(V_B,V_A,T_a),T_a) = c_union(V_B,V_A,T_a) ).

%------------------------------------------------------------------------------

```

### ./SWV005-1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-1 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for messages
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Message-simp2.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   51 (  19 unt;   9 nHn;  30 RR)
%            Number of literals    :   93 (  21 equ;  33 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :   18 (  18 usr;   3 con; 0-3 aty)
%            Number of variables   :  112 (   6 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax
%------------------------------------------------------------------------------
cnf(cls_Message_OAgent__synth_0,axiom,
    c_in(c_Message_Omsg_OAgent(V_A),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_OCrypt__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OHash__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_N),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_ONumber__synth_0,axiom,
    c_in(c_Message_Omsg_ONumber(V_n),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__Crypt__if_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__Crypt__if_1,axiom,
    ( c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__analzD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oanalz(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__empty_0,axiom,
    c_Message_Oanalz(c_emptyset) = c_emptyset ).

cnf(cls_Message_Oanalz__idem_0,axiom,
    c_Message_Oanalz(c_Message_Oanalz(V_H)) = c_Message_Oanalz(V_H) ).

cnf(cls_Message_Oanalz__insert__Agent_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OAgent(V_agt),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OAgent(V_agt),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Hash_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OHash(V_X),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Key_0,axiom,
    ( c_in(V_K,c_Message_OkeysFor(c_Message_Oanalz(V_H)),tc_nat)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OKey(V_K),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__insert__MPair_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(c_insert(V_X,c_insert(V_Y,V_H,tc_Message_Omsg),tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Nonce_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONonce(V_N),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Number_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_ONumber(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONumber(V_N),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__parts_0,axiom,
    c_Message_Oanalz(c_Message_Oparts(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oanalz__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Oanalz(V_G),c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oanalz__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oanalz(V_G),c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oin__parts__UnE_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_union(V_G,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_G),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__analz_0,axiom,
    c_Message_Oparts(c_Message_Oanalz(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oparts__cut__eq_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)) = c_Message_Oparts(V_H) ) ).

cnf(cls_Message_Oparts__idem_0,axiom,
    c_Message_Oparts(c_Message_Oparts(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oparts__insert__Agent_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OAgent(V_agt),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OAgent(V_agt),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Crypt_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Hash_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OHash(V_X),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Key_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OKey(V_K),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__MPair_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(c_insert(V_X,c_insert(V_Y,V_H,tc_Message_Omsg),tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Nonce_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Number_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_ONumber(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONumber(V_N),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__partsD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(c_Message_Oparts(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oparts__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Osynth_OCrypt_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OHash_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OMPair_0,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Osynth(V_G),c_Message_Osynth(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Osynth(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Osynth__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Osynth(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Osynth(V_G),c_Message_Osynth(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Osynth__synthD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(c_Message_Osynth(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-2.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-2 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for events
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Event-simp.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :  119 (  57 unt;  17 nHn;  78 RR)
%            Number of literals    :  200 (  87 equ;  83 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :   35 (  35 usr;  10 con; 0-3 aty)
%            Number of variables   :  324 ( 123 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OServer_A_58_Abad_A_61_61_AFalse_0,axiom,
    ~ c_in(c_Message_Oagent_OServer,c_Event_Obad,tc_Message_Oagent) ).

cnf(cls_Event_OSpy_A_58_Abad_A_61_61_ATrue_0,axiom,
    c_in(c_Message_Oagent_OSpy,c_Event_Obad,tc_Message_Oagent) ).

cnf(cls_Event_Oc_A_58_Aparts_A_Iknows_ASpy_Aevs1_J_A_61_61_62_Ac_A_58_Aused_Aevs1_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_c,c_Event_Oused(V_evs),tc_Message_Omsg) ) ).

cnf(cls_Event_Oevent_Odistinct__1_0,axiom,
    c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__2_0,axiom,
    c_Event_Oevent_OGets(V_agent_H,V_msg_H) != c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) ).

cnf(cls_Event_Oevent_Odistinct__3_0,axiom,
    c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__4_0,axiom,
    c_Event_Oevent_ONotes(V_agent_H,V_msg_H) != c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) ).

cnf(cls_Event_Oevent_Odistinct__5_0,axiom,
    c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__6_0,axiom,
    c_Event_Oevent_ONotes(V_agent_H,V_msg_H) != c_Event_Oevent_OGets(V_agent,V_msg) ).

cnf(cls_Event_Oevent_Oinject__1_0,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_agent1 = V_agent1_H ) ).

cnf(cls_Event_Oevent_Oinject__1_1,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_agent2 = V_agent2_H ) ).

cnf(cls_Event_Oevent_Oinject__1_2,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Event_Oevent_Oinject__2_0,axiom,
    ( c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Event_Oevent_Oinject__2_1,axiom,
    ( c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Event_Oevent_Oinject__3_0,axiom,
    ( c_Event_Oevent_ONotes(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Event_Oevent_Oinject__3_1,axiom,
    ( c_Event_Oevent_ONotes(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Event_Oevent_Osize__1_0,axiom,
    c_Nat_Osize(c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg),tc_Event_Oevent) = c_0 ).

cnf(cls_Event_Oevent_Osize__2_0,axiom,
    c_Nat_Osize(c_Event_Oevent_OGets(V_agent,V_msg),tc_Event_Oevent) = c_0 ).

cnf(cls_Event_Oevent_Osize__3_0,axiom,
    c_Nat_Osize(c_Event_Oevent_ONotes(V_agent,V_msg),tc_Event_Oevent) = c_0 ).

cnf(cls_Event_OkeysFor__synth_H_0,axiom,
    ( ~ c_in(V_K,c_Message_OkeysFor(c_Message_Osynth(V_H)),tc_nat)
    | c_in(V_K,c_Message_OkeysFor(V_H),tc_nat)
    | c_in(c_Message_Omsg_OKey(v_sko__uhi(V_H,V_K)),V_H,tc_Message_Omsg) ) ).

cnf(cls_Event_OkeysFor__synth_H_1,axiom,
    ( ~ c_in(V_K,c_Message_OkeysFor(c_Message_Osynth(V_H)),tc_nat)
    | c_in(V_K,c_Message_OkeysFor(V_H),tc_nat)
    | V_K = c_Message_OinvKey(v_sko__uhi(V_H,V_K)) ) ).

cnf(cls_Event_OkeysFor__synth_H_2,axiom,
    ( ~ c_in(V_K,c_Message_OkeysFor(V_H),tc_nat)
    | c_in(V_K,c_Message_OkeysFor(c_Message_Osynth(V_H)),tc_nat) ) ).

cnf(cls_Event_OkeysFor__synth_H_3,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_U),V_H,tc_Message_Omsg)
    | c_in(c_Message_OinvKey(V_U),c_Message_OkeysFor(c_Message_Osynth(V_H)),tc_nat) ) ).

cnf(cls_Event_Oknows_Oknows__Nil_0,axiom,
    c_Event_Oknows(V_A,c_List_Olist_ONil) = c_Event_OinitState(V_A) ).

cnf(cls_Event_Oknows__Spy__Gets_0,axiom,
    c_Event_Oknows(c_Message_Oagent_OSpy,c_List_Olist_OCons(c_Event_Oevent_OGets(V_A,V_X),V_evs,tc_Event_Oevent)) = c_Event_Oknows(c_Message_Oagent_OSpy,V_evs) ).

cnf(cls_Event_Oknows__Spy__Notes_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_Event_Oknows(c_Message_Oagent_OSpy,c_List_Olist_OCons(c_Event_Oevent_ONotes(V_A,V_X),V_evs,tc_Event_Oevent)) = c_insert(V_X,c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Event_Oknows__Spy__Notes_1,axiom,
    ( c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_Event_Oknows(c_Message_Oagent_OSpy,c_List_Olist_OCons(c_Event_Oevent_ONotes(V_A,V_X),V_evs,tc_Event_Oevent)) = c_Event_Oknows(c_Message_Oagent_OSpy,V_evs) ) ).

cnf(cls_Event_Oknows__Spy__Says_0,axiom,
    c_Event_Oknows(c_Message_Oagent_OSpy,c_List_Olist_OCons(c_Event_Oevent_OSays(V_A,V_B,V_X),V_evs,tc_Event_Oevent)) = c_insert(V_X,c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ).

cnf(cls_Event_Oused__Gets_0,axiom,
    c_Event_Oused(c_List_Olist_OCons(c_Event_Oevent_OGets(V_A,V_X),V_evs,tc_Event_Oevent)) = c_Event_Oused(V_evs) ).

cnf(cls_Event_Oused__Notes_0,axiom,
    c_Event_Oused(c_List_Olist_OCons(c_Event_Oevent_ONotes(V_A,V_X),V_evs,tc_Event_Oevent)) = c_union(c_Message_Oparts(c_insert(V_X,c_emptyset,tc_Message_Omsg)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Event_Oused__Says_0,axiom,
    c_Event_Oused(c_List_Olist_OCons(c_Event_Oevent_OSays(V_A,V_B,V_X),V_evs,tc_Event_Oevent)) = c_union(c_Message_Oparts(c_insert(V_X,c_emptyset,tc_Message_Omsg)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Message_OAgent__synth_0,axiom,
    c_in(c_Message_Omsg_OAgent(V_A),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_OCrypt__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__analz__eq_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_Message_Osynth(c_Message_Oanalz(c_insert(V_X,V_H,tc_Message_Omsg))) = c_Message_Osynth(c_Message_Oanalz(V_H)) ) ).

cnf(cls_Message_OHPair__eq_0,axiom,
    ( c_Message_OHPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_X_H = V_X ) ).

cnf(cls_Message_OHPair__eq_1,axiom,
    ( c_Message_OHPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OHPair__eq__MPair_0,axiom,
    ( c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OMPair(V_X_H,V_Y_H)
    | V_X_H = c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)) ) ).

cnf(cls_Message_OHPair__eq__MPair_1,axiom,
    ( c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OMPair(V_X_H,V_Y_H)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OHPair__eq__MPair_2,axiom,
    c_Message_OHPair(V_X,V_x) = c_Message_Omsg_OMPair(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_x)),V_x) ).

cnf(cls_Message_OHPair__neqs__1_0,axiom,
    c_Message_Omsg_OAgent(V_A) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__2_0,axiom,
    c_Message_Omsg_ONonce(V_N) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__3_0,axiom,
    c_Message_Omsg_ONumber(V_N) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__4_0,axiom,
    c_Message_Omsg_OKey(V_K) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__5_0,axiom,
    c_Message_Omsg_OHash(V_Z) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__6_0,axiom,
    c_Message_Omsg_OCrypt(V_K,V_X_H) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__synth__analz_0,axiom,
    ( ~ c_in(c_Message_OHPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OHPair__synth__analz_1,axiom,
    ( ~ c_in(c_Message_OHPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OHPair__synth__analz_2,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_OHPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_AAgent_AA2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OAgent(V_A) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_ACrypt_AK2_AX_H2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OCrypt(V_K,V_X_H) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_AHash_AZ2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OHash(V_Z) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_AKey_AK2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OKey(V_K) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_ANonce_AN2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_ONonce(V_N) ).

cnf(cls_Message_OHash_91X2_93_AY2_A_61_ANumber_AN2_A_61_61_AFalse_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_ONumber(V_N) ).

cnf(cls_Message_OHash__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OHash__synth__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OHash__synth__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__eq__HPair_0,axiom,
    ( c_Message_Omsg_OMPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_X_H = c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)) ) ).

cnf(cls_Message_OMPair__eq__HPair_1,axiom,
    ( c_Message_Omsg_OMPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OMPair__eq__HPair_2,axiom,
    c_Message_Omsg_OMPair(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_x)),V_x) = c_Message_OHPair(V_X,V_x) ).

cnf(cls_Message_OMPair__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz_2,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth__eq_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth__eq_1,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_N),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_ONumber__synth_0,axiom,
    c_in(c_Message_Omsg_ONumber(V_n),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__Crypt__if_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__Crypt__if_1,axiom,
    ( c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__analzD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oanalz(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__analz__Un_0,axiom,
    c_Message_Oanalz(c_union(c_Message_Oanalz(V_G),V_H,tc_Message_Omsg)) = c_Message_Oanalz(c_union(V_G,V_H,tc_Message_Omsg)) ).

cnf(cls_Message_Oanalz__conj__parts_0,axiom,
    ( ~ c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__empty_0,axiom,
    c_Message_Oanalz(c_emptyset) = c_emptyset ).

cnf(cls_Message_Oanalz__idem_0,axiom,
    c_Message_Oanalz(c_Message_Oanalz(V_H)) = c_Message_Oanalz(V_H) ).

cnf(cls_Message_Oanalz__insert__Agent_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OAgent(V_agt),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OAgent(V_agt),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__HPair_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_OHPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_OHPair(V_X,V_Y),c_insert(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oanalz(c_insert(V_Y,V_H,tc_Message_Omsg)),tc_Message_Omsg),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Hash_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OHash(V_X),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Key_0,axiom,
    ( c_in(V_K,c_Message_OkeysFor(c_Message_Oanalz(V_H)),tc_nat)
    | c_Message_Oanalz(c_insert(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OKey(V_K),c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__insert__MPair_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(c_insert(V_X,c_insert(V_Y,V_H,tc_Message_Omsg),tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Nonce_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONonce(V_N),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__insert__Number_0,axiom,
    c_Message_Oanalz(c_insert(c_Message_Omsg_ONumber(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONumber(V_N),c_Message_Oanalz(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__parts_0,axiom,
    c_Message_Oanalz(c_Message_Oparts(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oanalz__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Oanalz(V_G),c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oanalz__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oanalz(V_G),c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oanalz__synth_0,axiom,
    c_Message_Oanalz(c_Message_Osynth(V_H)) = c_union(c_Message_Oanalz(V_H),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oanalz__synth__Un_0,axiom,
    c_Message_Oanalz(c_union(c_Message_Osynth(V_G),V_H,tc_Message_Omsg)) = c_union(c_Message_Oanalz(c_union(V_G,V_H,tc_Message_Omsg)),c_Message_Osynth(V_G),tc_Message_Omsg) ).

cnf(cls_Message_Oin__parts__UnE_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_union(V_G,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_G),tc_Message_Omsg) ) ).

cnf(cls_Message_OkeysFor__insert__HPair_0,axiom,
    c_Message_OkeysFor(c_insert(c_Message_OHPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_Message_OkeysFor(V_H) ).

cnf(cls_Message_Oparts__analz_0,axiom,
    c_Message_Oparts(c_Message_Oanalz(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oparts__cut__eq_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)) = c_Message_Oparts(V_H) ) ).

cnf(cls_Message_Oparts__idem_0,axiom,
    c_Message_Oparts(c_Message_Oparts(V_H)) = c_Message_Oparts(V_H) ).

cnf(cls_Message_Oparts__insert__Agent_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OAgent(V_agt),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OAgent(V_agt),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Crypt_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__HPair_0,axiom,
    c_Message_Oparts(c_insert(c_Message_OHPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_OHPair(V_X,V_Y),c_insert(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)),c_Message_Oparts(c_insert(V_Y,V_H,tc_Message_Omsg)),tc_Message_Omsg),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Hash_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OHash(V_X),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Key_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OKey(V_K),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__MPair_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(c_insert(V_X,c_insert(V_Y,V_H,tc_Message_Omsg),tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Nonce_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_ONonce(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__insert__Number_0,axiom,
    c_Message_Oparts(c_insert(c_Message_Omsg_ONumber(V_N),V_H,tc_Message_Omsg)) = c_insert(c_Message_Omsg_ONumber(V_N),c_Message_Oparts(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__partsD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(c_Message_Oparts(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oparts__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oparts__synth_0,axiom,
    c_Message_Oparts(c_Message_Osynth(V_H)) = c_union(c_Message_Oparts(V_H),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Osynth_OCrypt_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OHash_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OMPair_0,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Osynth(V_G),c_Message_Osynth(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Osynth(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Osynth__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Osynth(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Osynth(V_G),c_Message_Osynth(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Osynth__synthD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(c_Message_Osynth(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-3.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-3 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for public, simplified
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Public-simp.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   42 (  32 unt;   0 nHn;  24 RR)
%            Number of literals    :   52 (  24 equ;  24 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   28 (  28 usr;  12 con; 0-4 aty)
%            Number of variables   :   92 (  69 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax, SWV005-2.ax
%------------------------------------------------------------------------------
cnf(cls_Public_OCrypt__notin__used__empty_0,axiom,
    ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Event_Oused(c_List_Olist_ONil),tc_Message_Omsg) ).

cnf(cls_Public_OMPair__used_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_OMPair__used_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_ONonce__notin__initState_0,axiom,
    ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(c_Event_OinitState(V_B)),tc_Message_Omsg) ).

cnf(cls_Public_ONonce__notin__used__empty_0,axiom,
    ~ c_in(c_Message_Omsg_ONonce(V_N),c_Event_Oused(c_List_Olist_ONil),tc_Message_Omsg) ).

cnf(cls_Public_OSpy__spies__bad__privateKey_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_OSpy__spies__bad__shrK_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_Oanalz__spies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ).

cnf(cls_Public_OinvKey__K_0,axiom,
    ( ~ c_in(V_y,c_Message_OsymKeys,tc_nat)
    | c_Message_OinvKey(V_y) = V_y ) ).

cnf(cls_Public_OinvKey__shrK_0,axiom,
    c_Message_OinvKey(c_Public_OshrK(V_A)) = c_Public_OshrK(V_A) ).

cnf(cls_Public_Okeymode_Ocases__1_0,axiom,
    c_Public_Okeymode_Okeymode__case(V_y,V_f2,c_Public_Okeymode_OSignature,T_a) = V_y ).

cnf(cls_Public_Okeymode_Ocases__2_0,axiom,
    c_Public_Okeymode_Okeymode__case(V_f1,V_y,c_Public_Okeymode_OEncryption,T_a) = V_y ).

cnf(cls_Public_Okeymode_Odistinct__1_0,axiom,
    c_Public_Okeymode_OSignature != c_Public_Okeymode_OEncryption ).

cnf(cls_Public_Okeymode_Odistinct__2_0,axiom,
    c_Public_Okeymode_OEncryption != c_Public_Okeymode_OSignature ).

cnf(cls_Public_Okeymode_Orecs__1_0,axiom,
    c_Public_Okeymode_Okeymode__rec(V_y,V_f2,c_Public_Okeymode_OSignature,T_a) = V_y ).

cnf(cls_Public_Okeymode_Orecs__2_0,axiom,
    c_Public_Okeymode_Okeymode__rec(V_f1,V_y,c_Public_Okeymode_OEncryption,T_a) = V_y ).

cnf(cls_Public_Okeymode_Osize__1_0,axiom,
    c_Nat_Osize(c_Public_Okeymode_OSignature,tc_Public_Okeymode) = c_0 ).

cnf(cls_Public_Okeymode_Osize__2_0,axiom,
    c_Nat_Osize(c_Public_Okeymode_OEncryption,tc_Public_Okeymode) = c_0 ).

cnf(cls_Public_OkeysFor__parts__initState_0,axiom,
    c_Message_OkeysFor(c_Message_Oparts(c_Event_OinitState(V_C))) = c_emptyset ).

cnf(cls_Public_Onot__symKeys__priK_0,axiom,
    ~ c_in(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_Onot__symKeys__pubK_0,axiom,
    ~ c_in(c_Public_OpublicKey(V_b,V_A),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OpriEK__noteq__shrK_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(c_Public_Okeymode_OEncryption,V_A)) != c_Public_OshrK(V_B) ).

cnf(cls_Public_OpriK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OpriK__neq__shrK_0,axiom,
    c_Public_OshrK(V_A) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_C)) ).

cnf(cls_Public_OprivateKey_Ab1_AA1_A_61_ApublicKey_Ac1_AA_H1_A_61_61_AFalse_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) != c_Public_OpublicKey(V_c,V_A_H) ).

cnf(cls_Public_OprivateKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpubK__neq__shrK_0,axiom,
    c_Public_OshrK(V_A) != c_Public_OpublicKey(V_b,V_C) ).

cnf(cls_Public_OpublicKey__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_OinitState(V_B),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__inject_0,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_b = V_c ) ).

cnf(cls_Public_OpublicKey__inject_1,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_A = V_A_H ) ).

cnf(cls_Public_OpublicKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__neq__privateKey_0,axiom,
    c_Public_OpublicKey(V_c,V_A_H) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) ).

cnf(cls_Public_OshrK_AX1_A_58_AsymKeys_A_61_61_ATrue_0,axiom,
    c_in(c_Public_OshrK(V_X),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OshrK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__knows_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(V_A,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__injective_0,axiom,
    ( c_Public_OshrK(V_x) != c_Public_OshrK(V_y)
    | V_x = V_y ) ).

cnf(cls_Public_OshrK__neq__priK_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(V_b,V_C)) != c_Public_OshrK(V_A) ).

cnf(cls_Public_OshrK__neq__pubK_0,axiom,
    c_Public_OpublicKey(V_b,V_C) != c_Public_OshrK(V_A) ).

cnf(cls_Public_Ospies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OsymKeys__invKey__iff_0,axiom,
    ( ~ c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat)
    | c_in(V_K,c_Message_OsymKeys,tc_nat) ) ).

cnf(cls_Public_OsymKeys__invKey__iff_1,axiom,
    ( ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat) ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-4.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-4 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Yahalom, simplified
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Yahalom-simp.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   0 unt;   0 nHn;   8 RR)
%            Number of literals    :   22 (   0 equ;  14 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :   19 (  19 usr;   6 con; 0-3 aty)
%            Number of variables   :   21 (   4 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax, SWV005-2.ax,
%            SWV005-3.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__parts__insert__in__Un__dest_0,axiom,
    ( ~ c_in(V_Z,c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Z,c_union(c_Message_Osynth(c_Message_Oanalz(V_H)),c_Message_Oparts(V_H),tc_Message_Omsg),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts_OBody__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_OGets__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_OSpy__analz__shrK_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_Yahalom_OSpy__analz__shrK_1,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_OSpy__see__shrK_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_Yahalom_OSpy__see__shrK_1,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-5.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-5 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Yahalom
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Yahalom.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   12 (   1 unt;   3 nHn;   8 RR)
%            Number of literals    :   30 (   2 equ;  16 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    9 (   2 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :   29 (  29 usr;   9 con; 0-4 aty)
%            Number of variables   :   63 (  23 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax, SWV005-2.ax,
%            SWV005-3.ax, SWV005-4.ax
%------------------------------------------------------------------------------
cnf(cls_Yahalom_OA__trusts__YM3_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OKey(V_K))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_OGets__imp__Says_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OSays(v_sko__wPE(V_B,V_X,V_evs),V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Gets_0,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OGets(V_A,V_X),V_evs,tc_Event_Oevent))
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Gets_1,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs)
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OGets(V_A,V_X),V_evs,tc_Event_Oevent)) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Notes_0,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_ONotes(V_A,V_X),V_evs,tc_Event_Oevent))
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Notes_1,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs)
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_ONotes(V_A,V_X),V_evs,tc_Event_Oevent)) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Says_0,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OSays(V_S,V_A,V_X),V_evs,tc_Event_Oevent))
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs)
    | c_Message_Oagent_OServer = V_S ) ).

cnf(cls_Yahalom_OKeyWithNonce__Says_1,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OSays(V_S,V_A,V_X),V_evs,tc_Event_Oevent))
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs)
    | V_X = c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_sko__2VZ(V_A,V_K,V_NB,V_X)),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(v_sko__2Va(V_A,V_K,V_NB,V_X),c_Message_Omsg_ONonce(V_NB))))),v_sko__2Vb(V_A,V_K,V_NB,V_X)) ) ).

cnf(cls_Yahalom_OKeyWithNonce__Says_2,axiom,
    c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_U),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_V,c_Message_Omsg_ONonce(V_NB))))),V_W)),V_evs,tc_Event_Oevent)) ).

cnf(cls_Yahalom_OKeyWithNonce__Says_3,axiom,
    ( ~ c_Yahalom_OKeyWithNonce(V_K,V_NB,V_evs)
    | c_Yahalom_OKeyWithNonce(V_K,V_NB,c_List_Olist_OCons(c_Event_Oevent_OSays(V_S,V_A,V_X),V_evs,tc_Event_Oevent)) ) ).

cnf(cls_Yahalom_OSays__Server__not__shrK_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(c_Public_OshrK(V_x)),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_Onew__keys__not__used_0,axiom,
    ( ~ c_in(V_K,c_Message_OkeysFor(c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs))),tc_nat)
    | ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | c_in(c_Message_Omsg_OKey(V_K),c_Event_Oused(V_evs),tc_Message_Omsg) ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-6.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-6 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Yahalom, A Said
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Yahalom__A_Said.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :    8 (   0 unt;   1 nHn;   8 RR)
%            Number of literals    :   28 (   4 equ;  19 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    9 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   24 (  24 usr;   9 con; 0-4 aty)
%            Number of variables   :   62 (  29 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax, SWV005-2.ax,
%            SWV005-3.ax, SWV005-4.ax, SWV005-5.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__knows__Spy_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_OCrypt__Spy__analz__bad_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),V_X),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Public_OCrypt__imp__keysFor_0,axiom,
    ( ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(V_K,c_Message_OkeysFor(V_H),tc_nat) ) ).

cnf(cls_Yahalom_OB__trusts__YM4__shrK_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OKey(V_K))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_B,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(v_sko__2ji(V_A,V_B,V_K,V_evs)),c_Message_Omsg_ONonce(v_sko__2jj(V_A,V_B,V_K,V_evs)))))),c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OKey(V_K))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_Ounique__session__keys_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_A = V_A_H ) ).

cnf(cls_Yahalom_Ounique__session__keys_1,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_B = V_B_H ) ).

cnf(cls_Yahalom_Ounique__session__keys_2,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_na = V_na_H ) ).

cnf(cls_Yahalom_Ounique__session__keys_3,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_nb = V_nb_H ) ).

%------------------------------------------------------------------------------

```

### ./SWV005-7.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV005-7 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Yahalom, Spy
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Yahalom__Spy.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   14 (   0 unt;   6 nHn;  14 RR)
%            Number of literals    :   61 (  11 equ;  38 neg)
%            Maximal clause size   :    6 (   4 avg)
%            Maximal term depth    :    8 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   23 (  23 usr;   7 con; 0-3 aty)
%            Number of variables   :  131 (  69 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-1.ax, SWV005-0.ax, SWV005-2.ax,
%            SWV005-3.ax, SWV005-4.ax, SWV005-5.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__spies_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_Oanalz__shrK__Decrypt_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_OSays__Server__imp__YM2_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(V_k,c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OGets(c_Message_Oagent_OServer,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OMPair(V_na,V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_OSays__unique__NB_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_S_H,c_Message_Omsg_OMPair(V_X_H,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA_H),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(V_C,V_S,c_Message_Omsg_OMPair(V_X,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_nb,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | V_NA_H = V_NA ) ).

cnf(cls_Yahalom_OSays__unique__NB_1,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_S_H,c_Message_Omsg_OMPair(V_X_H,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA_H),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(V_C,V_S,c_Message_Omsg_OMPair(V_X,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_nb,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | V_A_H = V_A ) ).

cnf(cls_Yahalom_OSays__unique__NB_2,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_S_H,c_Message_Omsg_OMPair(V_X_H,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA_H),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(V_C,V_S,c_Message_Omsg_OMPair(V_X,c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NA),V_nb))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_nb,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | V_B_H = V_B ) ).

cnf(cls_Yahalom_OSpy__not__see__encrypted__key_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OKey(V_K))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Message_Omsg_OKey(V_K),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_B,c_Event_Obad,tc_Message_Oagent)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Event_Oevent_ONotes(c_Message_Oagent_OSpy,c_Message_Omsg_OMPair(V_na,c_Message_Omsg_OMPair(V_nb,c_Message_Omsg_OKey(V_K)))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_Ono__nonce__YM1__YM2_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OMPair(V_na,c_Message_Omsg_ONonce(V_NB)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(V_NB),V_nb_H))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_NB),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_Osingle__Nonce__secrecy_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_KAB),c_Message_Omsg_OMPair(V_na,c_Message_Omsg_ONonce(V_NB_H))))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Message_Omsg_ONonce(V_NB),c_Message_Oanalz(c_insert(c_Message_Omsg_OKey(V_KAB),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_NB),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | V_NB = V_NB_H
    | V_KAB = c_Public_OshrK(v_sko__2VY(V_KAB)) ) ).

cnf(cls_Yahalom_Osingle__Nonce__secrecy_1,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_KAB),c_Message_Omsg_OMPair(V_na,c_Message_Omsg_ONonce(V_NB_H))))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Message_Omsg_ONonce(V_NB),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_NB),c_Message_Oanalz(c_insert(c_Message_Omsg_OKey(V_KAB),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg)),tc_Message_Omsg)
    | V_NB = V_NB_H
    | V_KAB = c_Public_OshrK(v_sko__2VY(V_KAB)) ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_A = V_A_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_1,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_B = V_B_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_2,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_na = V_na_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_3,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_nb = V_nb_H ) ).

%------------------------------------------------------------------------------

```

### ./SWV006-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV006-0 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for public
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Public.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   79 (  31 unt;   6 nHn;  75 RR)
%            Number of literals    :  136 (  72 equ;  77 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   24 (  24 usr;   6 con; 0-3 aty)
%            Number of variables   :  229 ( 119 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OServer_A_58_Abad_A_61_61_62_AR_0,axiom,
    ~ c_in(c_Message_Oagent_OServer,c_Event_Obad,tc_Message_Oagent) ).

cnf(cls_Event_OSpy_A_58_Abad_0,axiom,
    c_in(c_Message_Oagent_OSpy,c_Event_Obad,tc_Message_Oagent) ).

cnf(cls_Event_Oc_A_58_Aparts_A_Iknows_ASpy_Aevs1_J_A_61_61_62_Ac_A_58_Aused_Aevs1_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_c,c_Event_Oused(V_evs),tc_Message_Omsg) ) ).

cnf(cls_Event_Oevent_Odistinct__1__iff1_0,axiom,
    c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__2__iff1_0,axiom,
    c_Event_Oevent_OGets(V_agent_H,V_msg_H) != c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) ).

cnf(cls_Event_Oevent_Odistinct__3__iff1_0,axiom,
    c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__4__iff1_0,axiom,
    c_Event_Oevent_ONotes(V_agent_H,V_msg_H) != c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) ).

cnf(cls_Event_Oevent_Odistinct__5__iff1_0,axiom,
    c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H) ).

cnf(cls_Event_Oevent_Odistinct__6__iff1_0,axiom,
    c_Event_Oevent_ONotes(V_agent_H,V_msg_H) != c_Event_Oevent_OGets(V_agent,V_msg) ).

cnf(cls_Event_Oevent_Oinject__1__iff1_0,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_agent1 = V_agent1_H ) ).

cnf(cls_Event_Oevent_Oinject__1__iff1_1,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_agent2 = V_agent2_H ) ).

cnf(cls_Event_Oevent_Oinject__1__iff1_2,axiom,
    ( c_Event_Oevent_OSays(V_agent1,V_agent2,V_msg) != c_Event_Oevent_OSays(V_agent1_H,V_agent2_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Event_Oevent_Oinject__2__iff1_0,axiom,
    ( c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Event_Oevent_Oinject__2__iff1_1,axiom,
    ( c_Event_Oevent_OGets(V_agent,V_msg) != c_Event_Oevent_OGets(V_agent_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Event_Oevent_Oinject__3__iff1_0,axiom,
    ( c_Event_Oevent_ONotes(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Event_Oevent_Oinject__3__iff1_1,axiom,
    ( c_Event_Oevent_ONotes(V_agent,V_msg) != c_Event_Oevent_ONotes(V_agent_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_OCrypt__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OHPair__eq__MPair__iff1_0,axiom,
    ( c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OMPair(V_X_H,V_Y_H)
    | V_X_H = c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)) ) ).

cnf(cls_Message_OHPair__eq__MPair__iff1_1,axiom,
    ( c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OMPair(V_X_H,V_Y_H)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OHPair__eq__MPair__iff2_0,axiom,
    c_Message_OHPair(V_X,V_x) = c_Message_Omsg_OMPair(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_x)),V_x) ).

cnf(cls_Message_OHPair__eq__iff1_0,axiom,
    ( c_Message_OHPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_X_H = V_X ) ).

cnf(cls_Message_OHPair__eq__iff1_1,axiom,
    ( c_Message_OHPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OHPair__neqs__1__iff1_0,axiom,
    c_Message_Omsg_OAgent(V_A) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__2__iff1_0,axiom,
    c_Message_Omsg_ONonce(V_N) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__3__iff1_0,axiom,
    c_Message_Omsg_ONumber(V_N) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__4__iff1_0,axiom,
    c_Message_Omsg_OKey(V_K) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__5__iff1_0,axiom,
    c_Message_Omsg_OHash(V_Z) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHPair__neqs__6__iff1_0,axiom,
    c_Message_Omsg_OCrypt(V_K,V_X_H) != c_Message_OHPair(V_X,V_Y) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_AAgent_AA_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OAgent(V_A) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_ACrypt_AK_AX_H_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OCrypt(V_K,V_X_H) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_AHash_AZ_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OHash(V_Z) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_AKey_AK_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_OKey(V_K) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_ANonce_AN_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_ONonce(V_N) ).

cnf(cls_Message_OHash_91X_93_AY_A_61_ANumber_AN_A_61_61_62_AR_0,axiom,
    c_Message_OHPair(V_X,V_Y) != c_Message_Omsg_ONumber(V_N) ).

cnf(cls_Message_OHash__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OKey__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OKey(V_K),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__eq__HPair__iff1_0,axiom,
    ( c_Message_Omsg_OMPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_X_H = c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_Y)) ) ).

cnf(cls_Message_OMPair__eq__HPair__iff1_1,axiom,
    ( c_Message_Omsg_OMPair(V_X_H,V_Y_H) != c_Message_OHPair(V_X,V_Y)
    | V_Y_H = V_Y ) ).

cnf(cls_Message_OMPair__eq__HPair__iff2_0,axiom,
    c_Message_Omsg_OMPair(c_Message_Omsg_OHash(c_Message_Omsg_OMPair(V_X,V_x)),V_x) = c_Message_OHPair(V_X,V_x) ).

cnf(cls_Message_OMPair__parts_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz__iff1_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz__iff1_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz__iff2_0,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_ONonce__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_n),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(V_n),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_Oagent_Odistinct__1__iff1_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OFriend(V_nat_H) ).

cnf(cls_Message_Oagent_Odistinct__2__iff1_0,axiom,
    c_Message_Oagent_OFriend(V_nat_H) != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__3__iff1_0,axiom,
    c_Message_Oagent_OServer != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__4__iff1_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OServer ).

cnf(cls_Message_Oagent_Odistinct__5__iff1_0,axiom,
    c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OSpy ).

cnf(cls_Message_Oagent_Odistinct__6__iff1_0,axiom,
    c_Message_Oagent_OSpy != c_Message_Oagent_OFriend(V_nat) ).

cnf(cls_Message_Oagent_Oinject__iff1_0,axiom,
    ( c_Message_Oagent_OFriend(V_nat) != c_Message_Oagent_OFriend(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Oanalz_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__analzD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oanalz(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oin__parts__UnE_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_union(V_G,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_G),tc_Message_Omsg) ) ).

cnf(cls_Message_Omsg_Oinject__1__iff1_0,axiom,
    ( c_Message_Omsg_OAgent(V_agent) != c_Message_Omsg_OAgent(V_agent_H)
    | V_agent = V_agent_H ) ).

cnf(cls_Message_Omsg_Oinject__2__iff1_0,axiom,
    ( c_Message_Omsg_ONumber(V_nat) != c_Message_Omsg_ONumber(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__3__iff1_0,axiom,
    ( c_Message_Omsg_ONonce(V_nat) != c_Message_Omsg_ONonce(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__4__iff1_0,axiom,
    ( c_Message_Omsg_OKey(V_nat) != c_Message_Omsg_OKey(V_nat_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__5__iff1_0,axiom,
    ( c_Message_Omsg_OHash(V_msg) != c_Message_Omsg_OHash(V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Omsg_Oinject__6__iff1_0,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg1 = V_msg1_H ) ).

cnf(cls_Message_Omsg_Oinject__6__iff1_1,axiom,
    ( c_Message_Omsg_OMPair(V_msg1,V_msg2) != c_Message_Omsg_OMPair(V_msg1_H,V_msg2_H)
    | V_msg2 = V_msg2_H ) ).

cnf(cls_Message_Omsg_Oinject__7__iff1_0,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_nat = V_nat_H ) ).

cnf(cls_Message_Omsg_Oinject__7__iff1_1,axiom,
    ( c_Message_Omsg_OCrypt(V_nat,V_msg) != c_Message_Omsg_OCrypt(V_nat_H,V_msg_H)
    | V_msg = V_msg_H ) ).

cnf(cls_Message_Oparts_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts__emptyE_0,axiom,
    ~ c_in(V_X,c_Message_Oparts(c_emptyset),tc_Message_Omsg) ).

cnf(cls_Message_Oparts__partsD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Oparts(c_Message_Oparts(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OAgent_0,axiom,
    c_in(c_Message_Omsg_OAgent(V_agt),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Osynth_OCrypt_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OHash_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OHash(V_X),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OMPair_0,axiom,
    ( ~ c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_ONumber_0,axiom,
    c_in(c_Message_Omsg_ONumber(V_n),c_Message_Osynth(V_H),tc_Message_Omsg) ).

cnf(cls_Message_Osynth__synthD__dest_0,axiom,
    ( ~ c_in(V_X,c_Message_Osynth(c_Message_Osynth(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

%------------------------------------------------------------------------------

```

### ./SWV006-1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV006-1 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Otway Rees
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : OtwayRees.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   36 (  19 unt;   0 nHn;  24 RR)
%            Number of literals    :   59 (  12 equ;  32 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   31 (  31 usr;  10 con; 0-3 aty)
%            Number of variables   :   92 (  55 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax, SWV006-0.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__parts__insert__in__Un__dest_0,axiom,
    ( ~ c_in(V_Z,c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Z,c_union(c_Message_Osynth(c_Message_Oanalz(V_H)),c_Message_Oparts(V_H),tc_Message_Omsg),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__into__parts__dest_0,axiom,
    ( ~ c_in(V_c,c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts_OBody__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_OtwayRees_OGets__imp__Says__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OSays(v_sko__usf(V_B,V_X,V_evs),V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_OtwayRees_OSpy__see__shrK__D__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_OtwayRees_Ono__nonce__OR1__OR2__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(V_NA_H,c_Message_Omsg_OMPair(V_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A_H),c_Message_Omsg_OAgent(V_A))))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(V_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OAgent(V_B)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_Public_OMPair__used_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_OMPair__used_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_ONonce__notin__initState__iff1_0,axiom,
    ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(c_Event_OinitState(V_B)),tc_Message_Omsg) ).

cnf(cls_Public_OSpy__spies__bad__privateKey_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_OSpy__spies__bad__shrK_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_Oanalz__spies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ).

cnf(cls_Public_Okeymode_Odistinct__1__iff1_0,axiom,
    c_Public_Okeymode_OSignature != c_Public_Okeymode_OEncryption ).

cnf(cls_Public_Okeymode_Odistinct__2__iff1_0,axiom,
    c_Public_Okeymode_OEncryption != c_Public_Okeymode_OSignature ).

cnf(cls_Public_Onot__symKeys__priK__iff1_0,axiom,
    ~ c_in(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_Onot__symKeys__pubK__iff1_0,axiom,
    ~ c_in(c_Public_OpublicKey(V_b,V_A),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OpriK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OpriK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_C)) ).

cnf(cls_Public_OprivateKey_Ab_AA_A_61_ApublicKey_Ac_AA_H_A_61_61_62_AR_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) != c_Public_OpublicKey(V_c,V_A_H) ).

cnf(cls_Public_OprivateKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpubK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Public_OpublicKey(V_b,V_C) ).

cnf(cls_Public_OpublicKey__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_OinitState(V_B),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__inject__iff1_0,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_b = V_c ) ).

cnf(cls_Public_OpublicKey__inject__iff1_1,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_A = V_A_H ) ).

cnf(cls_Public_OpublicKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__neq__privateKey__iff1_0,axiom,
    c_Public_OpublicKey(V_c,V_A_H) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) ).

cnf(cls_Public_OshrK_AX_A_58_AsymKeys_0,axiom,
    c_in(c_Public_OshrK(V_X),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OshrK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__knows_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(V_A,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__injective__iff1_0,axiom,
    ( c_Public_OshrK(V_x) != c_Public_OshrK(V_y)
    | V_x = V_y ) ).

cnf(cls_Public_Ospies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff1_0,axiom,
    ( ~ c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat)
    | c_in(V_K,c_Message_OsymKeys,tc_nat) ) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff2_0,axiom,
    ( ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat) ) ).

%------------------------------------------------------------------------------

```

### ./SWV006-2.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV006-2 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Otway Rees, version 2
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : OtwayRees2.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   34 (  19 unt;   0 nHn;  22 RR)
%            Number of literals    :   52 (  12 equ;  27 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   30 (  30 usr;  10 con; 0-3 aty)
%            Number of variables   :   84 (  52 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax, SWV006-0.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__parts__insert__in__Un__dest_0,axiom,
    ( ~ c_in(V_Z,c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Z,c_union(c_Message_Osynth(c_Message_Oanalz(V_H)),c_Message_Oparts(V_H),tc_Message_Omsg),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__into__parts__dest_0,axiom,
    ( ~ c_in(V_c,c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts_OBody__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_OtwayRees_OGets__imp__Says__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OSays(v_sko__usf(V_B,V_X,V_evs),V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Public_OMPair__used_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_OMPair__used_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_ONonce__notin__initState__iff1_0,axiom,
    ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(c_Event_OinitState(V_B)),tc_Message_Omsg) ).

cnf(cls_Public_OSpy__spies__bad__privateKey_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_OSpy__spies__bad__shrK_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_Oanalz__spies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ).

cnf(cls_Public_Okeymode_Odistinct__1__iff1_0,axiom,
    c_Public_Okeymode_OSignature != c_Public_Okeymode_OEncryption ).

cnf(cls_Public_Okeymode_Odistinct__2__iff1_0,axiom,
    c_Public_Okeymode_OEncryption != c_Public_Okeymode_OSignature ).

cnf(cls_Public_Onot__symKeys__priK__iff1_0,axiom,
    ~ c_in(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_Onot__symKeys__pubK__iff1_0,axiom,
    ~ c_in(c_Public_OpublicKey(V_b,V_A),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OpriK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OpriK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_C)) ).

cnf(cls_Public_OprivateKey_Ab_AA_A_61_ApublicKey_Ac_AA_H_A_61_61_62_AR_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) != c_Public_OpublicKey(V_c,V_A_H) ).

cnf(cls_Public_OprivateKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpubK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Public_OpublicKey(V_b,V_C) ).

cnf(cls_Public_OpublicKey__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_OinitState(V_B),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__inject__iff1_0,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_b = V_c ) ).

cnf(cls_Public_OpublicKey__inject__iff1_1,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_A = V_A_H ) ).

cnf(cls_Public_OpublicKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__neq__privateKey__iff1_0,axiom,
    c_Public_OpublicKey(V_c,V_A_H) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) ).

cnf(cls_Public_OshrK_AX_A_58_AsymKeys_0,axiom,
    c_in(c_Public_OshrK(V_X),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OshrK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__knows_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(V_A,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__injective__iff1_0,axiom,
    ( c_Public_OshrK(V_x) != c_Public_OshrK(V_y)
    | V_x = V_y ) ).

cnf(cls_Public_Ospies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff1_0,axiom,
    ( ~ c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat)
    | c_in(V_K,c_Message_OsymKeys,tc_nat) ) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff2_0,axiom,
    ( ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat) ) ).

%------------------------------------------------------------------------------

```

### ./SWV006-3.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV006-3 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification
% Axioms   : Cryptographic protocol axioms for Yahalom, version B
% Version  : [Pau06] axioms.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Yahalom__B.ax [Pau06]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   43 (  19 unt;   1 nHn;  31 RR)
%            Number of literals    :   83 (  16 equ;  48 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :   32 (  32 usr;  11 con; 0-3 aty)
%            Number of variables   :  150 (  81 sgn)
% SPC      : 

% Comments : Requires MSC001-0.ax, MSC001-2.ax, SWV006-0.ax
%------------------------------------------------------------------------------
cnf(cls_Event_OSays__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Event_OSays__imp__spies_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__parts__insert__in__Un__dest_0,axiom,
    ( ~ c_in(V_Z,c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Z,c_union(c_Message_Osynth(c_Message_Oanalz(V_H)),c_Message_Oparts(V_H),tc_Message_Omsg),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_ODecrypt__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | ~ c_in(c_Message_Omsg_OKey(c_Message_OinvKey(V_K)),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__into__parts__dest_0,axiom,
    ( ~ c_in(V_c,c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts_OBody__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_OCrypt__Spy__analz__bad_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),V_X),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Public_OMPair__used_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_OMPair__used_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Event_Oused(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Event_Oused(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_ONonce__notin__initState__iff1_0,axiom,
    ~ c_in(c_Message_Omsg_ONonce(V_N),c_Message_Oparts(c_Event_OinitState(V_B)),tc_Message_Omsg) ).

cnf(cls_Public_OSpy__spies__bad__privateKey_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_OSpy__spies__bad__shrK_0,axiom,
    ( ~ c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ) ).

cnf(cls_Public_Oanalz__spies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ).

cnf(cls_Public_Okeymode_Odistinct__1__iff1_0,axiom,
    c_Public_Okeymode_OSignature != c_Public_Okeymode_OEncryption ).

cnf(cls_Public_Okeymode_Odistinct__2__iff1_0,axiom,
    c_Public_Okeymode_OEncryption != c_Public_Okeymode_OSignature ).

cnf(cls_Public_Onot__symKeys__priK__iff1_0,axiom,
    ~ c_in(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_Onot__symKeys__pubK__iff1_0,axiom,
    ~ c_in(c_Public_OpublicKey(V_b,V_A),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OpriK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OpriK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_C)) ).

cnf(cls_Public_OprivateKey_Ab_AA_A_61_ApublicKey_Ac_AA_H_A_61_61_62_AR_0,axiom,
    c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) != c_Public_OpublicKey(V_c,V_A_H) ).

cnf(cls_Public_OprivateKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A))),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpubK__neq__shrK__iff1_0,axiom,
    c_Public_OshrK(V_A) != c_Public_OpublicKey(V_b,V_C) ).

cnf(cls_Public_OpublicKey__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_OinitState(V_B),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__inject__iff1_0,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_b = V_c ) ).

cnf(cls_Public_OpublicKey__inject__iff1_1,axiom,
    ( c_Public_OpublicKey(V_b,V_A) != c_Public_OpublicKey(V_c,V_A_H)
    | V_A = V_A_H ) ).

cnf(cls_Public_OpublicKey__into__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OpublicKey__neq__privateKey__iff1_0,axiom,
    c_Public_OpublicKey(V_c,V_A_H) != c_Message_OinvKey(c_Public_OpublicKey(V_b,V_A)) ).

cnf(cls_Public_OshrK_AX_A_58_AsymKeys_0,axiom,
    c_in(c_Public_OshrK(V_X),c_Message_OsymKeys,tc_nat) ).

cnf(cls_Public_OshrK__in__initState_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_OinitState(V_A),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__knows_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oknows(V_A,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__in__used_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Event_Oused(V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OshrK__injective__iff1_0,axiom,
    ( c_Public_OshrK(V_x) != c_Public_OshrK(V_y)
    | V_x = V_y ) ).

cnf(cls_Public_Ospies__pubK_0,axiom,
    c_in(c_Message_Omsg_OKey(c_Public_OpublicKey(V_b,V_A)),c_Event_Oknows(c_Message_Oagent_OSpy,V_evs),tc_Message_Omsg) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff1_0,axiom,
    ( ~ c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat)
    | c_in(V_K,c_Message_OsymKeys,tc_nat) ) ).

cnf(cls_Public_OsymKeys__invKey__iff__iff2_0,axiom,
    ( ~ c_in(V_K,c_Message_OsymKeys,tc_nat)
    | c_in(c_Message_OinvKey(V_K),c_Message_OsymKeys,tc_nat) ) ).

cnf(cls_Yahalom_OA__trusts__YM3_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent)
    | c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),c_Message_Omsg_OCrypt(c_Public_OshrK(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_A),c_Message_Omsg_OKey(V_K))))),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_OGets__imp__Says_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OSays(v_sko__wPE(V_B,V_X,V_evs),V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_Yahalom_OGets__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Yahalom_OSpy__see__shrK__D__dest_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_0,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_A = V_A_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_1,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_B = V_B_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_2,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_na = V_na_H ) ).

cnf(cls_Yahalom_Ounique__session__keys__dest_3,axiom,
    ( ~ c_in(V_evs,c_Yahalom_Oyahalom,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A_H,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A_H),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B_H),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na_H,V_nb_H)))),V_X_H)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Event_Oevent_OSays(c_Message_Oagent_OServer,V_A,c_Message_Omsg_OMPair(c_Message_Omsg_OCrypt(c_Public_OshrK(V_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(V_B),c_Message_Omsg_OMPair(c_Message_Omsg_OKey(V_K),c_Message_Omsg_OMPair(V_na,V_nb)))),V_X)),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | V_nb = V_nb_H ) ).

%------------------------------------------------------------------------------

```

### ./SWV007+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV007+0 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Software Verification
% Axioms   : Priority queue checker: quasi-order set with bottom element
% Version  : [dNP05] axioms.
% English  :

% Refs     : [Pis06] Piskac (2006), Email to Geoff Sutcliffe
%          : [dNP05] de Nivelle & Piskac (2005), Verification of an Off-Lin
% Source   : [Pis06]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    5 (   2 unt;   0 def)
%            Number of atoms       :   10 (   0 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :    6 (   1   ~;   1   |;   2   &)
%                                         (   1 <=>;   1  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   4 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   1 con; 0-0 aty)
%            Number of variables   :    9 (   9   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(transitivity,axiom,
    ! [U,V,W] :
      ( ( less_than(U,V)
        & less_than(V,W) )
     => less_than(U,W) ) ).

fof(totality,axiom,
    ! [U,V] :
      ( less_than(U,V)
      | less_than(V,U) ) ).

fof(reflexivity,axiom,
    ! [U] : less_than(U,U) ).

fof(stricly_smaller_definition,axiom,
    ! [U,V] :
      ( strictly_less_than(U,V)
    <=> ( less_than(U,V)
        & ~ less_than(V,U) ) ) ).

fof(bottom_smallest,axiom,
    ! [U] : less_than(bottom,U) ).

%------------------------------------------------------------------------------


```

### ./SWV007+1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV007+1 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Software Verification
% Axioms   : Priority queue checker: priority queues
% Version  : [dNP05] axioms.
% English  : Priority queues are inductively defined.

% Refs     : [Pis06] Piskac (2006), Email to Geoff Sutcliffe
%          : [dNP05] de Nivelle & Piskac (2005), Verification of an Off-Lin
% Source   : [Pis06]
% Names    :

% Status   : Satisfiable
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : Number of formulae    :   12 (   5 unt;   0 def)
%            Number of atoms       :   26 (   9 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :   17 (   3   ~;   1   |;   5   &)
%                                         (   2 <=>;   6  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :    7 (   7 usr;   1 con; 0-2 aty)
%            Number of variables   :   25 (  25   !;   0   ?)
% SPC      : 

% Comments : Requires SWV007+0
%------------------------------------------------------------------------------
fof(ax6,axiom,
    ~ isnonempty_pq(create_pq) ).

fof(ax7,axiom,
    ! [U,V] : isnonempty_pq(insert_pq(U,V)) ).

fof(ax8,axiom,
    ! [U] : ~ contains_pq(create_pq,U) ).

fof(ax9,axiom,
    ! [U,V,W] :
      ( contains_pq(insert_pq(U,V),W)
    <=> ( contains_pq(U,W)
        | V = W ) ) ).

fof(ax10,axiom,
    ! [U,V] :
      ( issmallestelement_pq(U,V)
    <=> ! [W] :
          ( contains_pq(U,W)
         => less_than(V,W) ) ) ).

fof(ax11,axiom,
    ! [U,V] : remove_pq(insert_pq(U,V),V) = U ).

fof(ax12,axiom,
    ! [U,V,W] :
      ( ( contains_pq(U,W)
        & V != W )
     => remove_pq(insert_pq(U,V),W) = insert_pq(remove_pq(U,W),V) ) ).

fof(ax13,axiom,
    ! [U,V] :
      ( ( contains_pq(U,V)
        & issmallestelement_pq(U,V) )
     => findmin_pq_eff(U,V) = U ) ).

fof(ax14,axiom,
    ! [U,V] :
      ( ( contains_pq(U,V)
        & issmallestelement_pq(U,V) )
     => findmin_pq_res(U,V) = V ) ).

fof(ax15,axiom,
    ! [U,V] :
      ( ( contains_pq(U,V)
        & issmallestelement_pq(U,V) )
     => removemin_pq_eff(U,V) = remove_pq(U,V) ) ).

fof(ax16,axiom,
    ! [U,V] :
      ( ( contains_pq(U,V)
        & issmallestelement_pq(U,V) )
     => removemin_pq_res(U,V) = V ) ).

fof(ax17,axiom,
    ! [U,V,W] : insert_pq(insert_pq(U,V),W) = insert_pq(insert_pq(U,W),V) ).

%------------------------------------------------------------------------------

```

### ./SWV007+2.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV007+2 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Software Verification
% Axioms   : Priority queue checker: system of lower bounds
% Version  : [dNP05] axioms.
% English  :

% Refs     : [Pis06] Piskac (2006), Email to Geoff Sutcliffe
%          : [dNP05] de Nivelle & Piskac (2005), Verification of an Off-Lin
% Source   : [Pis06]
% Names    :

% Status   : Satisfiable
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : Number of formulae    :   13 (   7 unt;   0 def)
%            Number of atoms       :   24 (  12 equ)
%            Maximal formula atoms :    4 (   1 avg)
%            Number of connectives :   16 (   5   ~;   2   |;   3   &)
%                                         (   2 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    9 (   5 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :    6 (   6 usr;   1 con; 0-2 aty)
%            Number of variables   :   38 (  38   !;   0   ?)
% SPC      : 

% Comments : Requires SWV007+0
%------------------------------------------------------------------------------
fof(ax18,axiom,
    ~ isnonempty_slb(create_slb) ).

fof(ax19,axiom,
    ! [U,V,W] : isnonempty_slb(insert_slb(U,pair(V,W))) ).

fof(ax20,axiom,
    ! [U] : ~ contains_slb(create_slb,U) ).

fof(ax21,axiom,
    ! [U,V,W,X] :
      ( contains_slb(insert_slb(U,pair(V,X)),W)
    <=> ( contains_slb(U,W)
        | V = W ) ) ).

fof(ax22,axiom,
    ! [U,V] : ~ pair_in_list(create_slb,U,V) ).

fof(ax23,axiom,
    ! [U,V,W,X,Y] :
      ( pair_in_list(insert_slb(U,pair(V,X)),W,Y)
    <=> ( pair_in_list(U,W,Y)
        | ( V = W
          & X = Y ) ) ) ).

fof(ax24,axiom,
    ! [U,V,W] : remove_slb(insert_slb(U,pair(V,W)),V) = U ).

fof(ax25,axiom,
    ! [U,V,W,X] :
      ( ( V != W
        & contains_slb(U,W) )
     => remove_slb(insert_slb(U,pair(V,X)),W) = insert_slb(remove_slb(U,W),pair(V,X)) ) ).

fof(ax26,axiom,
    ! [U,V,W] : lookup_slb(insert_slb(U,pair(V,W)),V) = W ).

fof(ax27,axiom,
    ! [U,V,W,X] :
      ( ( V != W
        & contains_slb(U,W) )
     => lookup_slb(insert_slb(U,pair(V,X)),W) = lookup_slb(U,W) ) ).

fof(ax28,axiom,
    ! [U] : update_slb(create_slb,U) = create_slb ).

fof(ax29,axiom,
    ! [U,V,W,X] :
      ( strictly_less_than(X,W)
     => update_slb(insert_slb(U,pair(V,X)),W) = insert_slb(update_slb(U,W),pair(V,W)) ) ).

fof(ax30,axiom,
    ! [U,V,W,X] :
      ( less_than(W,X)
     => update_slb(insert_slb(U,pair(V,X)),W) = insert_slb(update_slb(U,W),pair(V,X)) ) ).

%------------------------------------------------------------------------------

```

### ./SWV007+3.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV007+3 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Software Verification
% Axioms   : Priority queue checker: checked priority queues
% Version  : [dNP05] axioms.
% English  : This axiom set fully describes checked priority queues. Checked
%            priority queues are defined as triples of a "priority queue
%            pretender", a system of lower bounds and Boolean value that keep
%            track of errors.

% Refs     : [Pis06] Piskac (2006), Email to Geoff Sutcliffe
%          : [dNP05] de Nivelle & Piskac (2005), Verification of an Off-Lin
% Source   : [Pis06]
% Names    :

% Status   : Satisfiable
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : Number of formulae    :   23 (   7 unt;   0 def)
%            Number of atoms       :   48 (  17 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   32 (   7   ~;   0   |;   7   &)
%                                         (   4 <=>;  14  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   5 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    9 (   7 usr;   1 prp; 0-2 aty)
%            Number of functors    :   18 (  18 usr;   3 con; 0-3 aty)
%            Number of variables   :   70 (  70   !;   0   ?)
% SPC      : 

% Comments : Requires SWV007+0 SWV007+2
%------------------------------------------------------------------------------
fof(ax31,axiom,
    ! [U] : succ_cpq(U,U) ).

fof(ax32,axiom,
    ! [U,V,W] :
      ( succ_cpq(U,V)
     => succ_cpq(U,insert_cpq(V,W)) ) ).

fof(ax33,axiom,
    ! [U,V,W] :
      ( succ_cpq(U,V)
     => succ_cpq(U,remove_cpq(V,W)) ) ).

fof(ax34,axiom,
    ! [U,V] :
      ( succ_cpq(U,V)
     => succ_cpq(U,findmin_cpq_eff(V)) ) ).

fof(ax35,axiom,
    ! [U,V] :
      ( succ_cpq(U,V)
     => succ_cpq(U,removemin_cpq_eff(V)) ) ).

fof(ax36,axiom,
    ! [U,V] : check_cpq(triple(U,create_slb,V)) ).

fof(ax37,axiom,
    ! [U,V,W,X,Y] :
      ( less_than(Y,X)
     => ( check_cpq(triple(U,insert_slb(V,pair(X,Y)),W))
      <=> check_cpq(triple(U,V,W)) ) ) ).

fof(ax38,axiom,
    ! [U,V,W,X,Y] :
      ( strictly_less_than(X,Y)
     => ( check_cpq(triple(U,insert_slb(V,pair(X,Y)),W))
      <=> $false ) ) ).

fof(ax39,axiom,
    ! [U,V,W,X] :
      ( contains_cpq(triple(U,V,W),X)
    <=> contains_slb(V,X) ) ).

fof(ax40,axiom,
    ! [U,V] :
      ( ok(triple(U,V,bad))
    <=> $false ) ).

fof(ax41,axiom,
    ! [U,V,W] :
      ( ~ ok(triple(U,V,W))
     => W = bad ) ).

fof(ax42,axiom,
    ! [U,V,W,X] : insert_cpq(triple(U,V,W),X) = triple(insert_pqp(U,X),insert_slb(V,pair(X,bottom)),W) ).

fof(ax43,axiom,
    ! [U,V,W,X] :
      ( ~ contains_slb(V,X)
     => remove_cpq(triple(U,V,W),X) = triple(U,V,bad) ) ).

fof(ax44,axiom,
    ! [U,V,W,X] :
      ( ( contains_slb(V,X)
        & less_than(lookup_slb(V,X),X) )
     => remove_cpq(triple(U,V,W),X) = triple(remove_pqp(U,X),remove_slb(V,X),W) ) ).

fof(ax45,axiom,
    ! [U,V,W,X] :
      ( ( contains_slb(V,X)
        & strictly_less_than(X,lookup_slb(V,X)) )
     => remove_cpq(triple(U,V,W),X) = triple(remove_pqp(U,X),remove_slb(V,X),bad) ) ).

fof(ax46,axiom,
    ! [U,V] : findmin_cpq_eff(triple(U,create_slb,V)) = triple(U,create_slb,bad) ).

fof(ax47,axiom,
    ! [U,V,W,X] :
      ( ( V != create_slb
        & ~ contains_slb(V,findmin_pqp_res(U)) )
     => findmin_cpq_eff(triple(U,V,W)) = triple(U,update_slb(V,findmin_pqp_res(U)),bad) ) ).

fof(ax48,axiom,
    ! [U,V,W,X] :
      ( ( V != create_slb
        & contains_slb(V,findmin_pqp_res(U))
        & strictly_less_than(findmin_pqp_res(U),lookup_slb(V,findmin_pqp_res(U))) )
     => findmin_cpq_eff(triple(U,V,W)) = triple(U,update_slb(V,findmin_pqp_res(U)),bad) ) ).

fof(ax49,axiom,
    ! [U,V,W,X] :
      ( ( V != create_slb
        & contains_slb(V,findmin_pqp_res(U))
        & less_than(lookup_slb(V,findmin_pqp_res(U)),findmin_pqp_res(U)) )
     => findmin_cpq_eff(triple(U,V,W)) = triple(U,update_slb(V,findmin_pqp_res(U)),W) ) ).

fof(ax50,axiom,
    ! [U,V] : findmin_cpq_res(triple(U,create_slb,V)) = bottom ).

fof(ax51,axiom,
    ! [U,V,W,X] :
      ( V != create_slb
     => findmin_cpq_res(triple(U,V,W)) = findmin_pqp_res(U) ) ).

fof(ax52,axiom,
    ! [U] : removemin_cpq_eff(U) = remove_cpq(findmin_cpq_eff(U),findmin_cpq_res(U)) ).

fof(ax53,axiom,
    ! [U] : removemin_cpq_res(U) = findmin_cpq_res(U) ).

%------------------------------------------------------------------------------

```

### ./SWV007+4.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV007+4 : TPTP v8.2.0. Released v3.3.0.
% Domain   : Software Verification
% Axioms   : Priority queue checker: implementation function, Pi, Pi#
% Version  : [dNP05] axioms.
% English  :

% Refs     : [Pis06] Piskac (2006), Email to Geoff Sutcliffe
%          : [dNP05] de Nivelle & Piskac (2005), Verification of an Off-Lin
% Source   : [Pis06]
% Names    :

% Status   : Satisfiable
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : Number of formulae    :    9 (   2 unt;   0 def)
%            Number of atoms       :   20 (   2 equ)
%            Maximal formula atoms :    4 (   2 avg)
%            Number of connectives :   11 (   0   ~;   0   |;   4   &)
%                                         (   7 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    6 (   5 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :   13 (  12 usr;   0 prp; 1-2 aty)
%            Number of functors    :    7 (   7 usr;   2 con; 0-3 aty)
%            Number of variables   :   21 (  18   !;   3   ?)
% SPC      : 

% Comments : Requires SWV007+0 SWV007+1 SWV007+2 SWV007+3
%------------------------------------------------------------------------------
fof(ax54,axiom,
    ! [U,V] : i(triple(U,create_slb,V)) = create_pq ).

fof(ax55,axiom,
    ! [U,V,W,X,Y] : i(triple(U,insert_slb(V,pair(X,Y)),W)) = insert_pq(i(triple(U,V,W)),X) ).

%----All below here are definitions
fof(ax56,axiom,
    ! [U,V] :
      ( pi_sharp_remove(U,V)
    <=> contains_pq(U,V) ) ).

fof(ax57,axiom,
    ! [U,V] :
      ( pi_remove(U,V)
    <=> pi_sharp_remove(i(U),V) ) ).

fof(ax58,axiom,
    ! [U,V] :
      ( pi_sharp_find_min(U,V)
    <=> ( contains_pq(U,V)
        & issmallestelement_pq(U,V) ) ) ).

fof(ax59,axiom,
    ! [U] :
      ( pi_find_min(U)
    <=> ? [V] : pi_sharp_find_min(i(U),V) ) ).

fof(ax60,axiom,
    ! [U,V] :
      ( pi_sharp_removemin(U,V)
    <=> ( contains_pq(U,V)
        & issmallestelement_pq(U,V) ) ) ).

fof(ax61,axiom,
    ! [U] :
      ( pi_removemin(U)
    <=> ? [V] : pi_sharp_find_min(i(U),V) ) ).

fof(ax62,axiom,
    ! [U] :
      ( phi(U)
    <=> ? [V] :
          ( succ_cpq(U,V)
          & ok(V)
          & check_cpq(V) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV008^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV008^0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Software Verification (Security)
% Axioms   : ICL logic based upon modal logic based upon simple type theory
% Version  : [Ben08] axioms.
% English  :

% Refs     : [GA08]  Garg & Abadi (2008), A Modal Deconstruction of Access
%          : [Ben08] Benzmueller (2008), Automating Access Control Logics i
%          : [BP09]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   19 (   9 unt;  10 typ;   9 def)
%            Number of atoms       :   31 (   9 equ;   0 cnn)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :   15 (   0   ~;   0   |;   0   &;  15   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;  15 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   43 (  43   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   18 (  17 usr;   7 con; 0-3 aty)
%            Number of variables   :   11 (  11   ^   0   !;   0   ?;  11   :)
% SPC      : 

% Comments : Requires LCL008^0.ax
%          : THF0 syntax
%------------------------------------------------------------------------------
%----The encoding of ICL logic employs only one accessibility relation which
%----introduce here as a constant 'rel'; we don't need multimodal logic.
thf(rel_type,type,
    rel: $i > $i > $o ).

%----ICL logic distiguishes between atoms and principals; for this we introduce
%----a predicate 'icl_atom' ...
thf(icl_atom_type,type,
    icl_atom: ( $i > $o ) > $i > $o ).

thf(icl_atom,definition,
    ( icl_atom
    = ( ^ [P: $i > $o] : ( mbox @ rel @ P ) ) ) ).

%---- ... and also a predicate 'icl_princ'
thf(icl_princ_type,type,
    icl_princ: ( $i > $o ) > $i > $o ).

thf(icl_princ,definition,
    ( icl_princ
    = ( ^ [P: $i > $o] : P ) ) ).

%----ICL and connective
thf(icl_and_type,type,
    icl_and: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(icl_and,definition,
    ( icl_and
    = ( ^ [A: $i > $o,B: $i > $o] : ( mand @ A @ B ) ) ) ).

%----ICL or connective
thf(icl_or_type,type,
    icl_or: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(icl_or,definition,
    ( icl_or
    = ( ^ [A: $i > $o,B: $i > $o] : ( mor @ A @ B ) ) ) ).

%----ICL implication connective
thf(icl_impl_type,type,
    icl_impl: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(icl_impl,definition,
    ( icl_impl
    = ( ^ [A: $i > $o,B: $i > $o] : ( mbox @ rel @ ( mimpl @ A @ B ) ) ) ) ).

%----ICL true connective
thf(icl_true_type,type,
    icl_true: $i > $o ).

thf(icl_true,definition,
    icl_true = mtrue ).

%----ICL false connective
thf(icl_false_type,type,
    icl_false: $i > $o ).

thf(icl_false,definition,
    icl_false = mfalse ).

%----ICL says connective
thf(icl_says_type,type,
    icl_says: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(icl_says,definition,
    ( icl_says
    = ( ^ [A: $i > $o,S: $i > $o] : ( mbox @ rel @ ( mor @ A @ S ) ) ) ) ).

%----An ICL formula is K-valid if its translation into modal logic is valid
thf(iclval_decl_type,type,
    iclval: ( $i > $o ) > $o ).

thf(icl_s4_valid,definition,
    ( iclval
    = ( ^ [X: $i > $o] : ( mvalid @ X ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV008^1.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV008^1 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Software Verification (Security)
% Axioms   : ICL notions of validity wrt S4
% Version  : [Ben08] axioms.
% English  :

% Refs     : [GA08]  Garg & Abadi (2008), A Modal Deconstruction of Access
%          : [Ben08] Benzmueller (2008), Automating Access Control Logics i
%          : [BP09]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   0 unt;   0 typ;   0 def)
%            Number of atoms       :   12 (   0 equ;   0 cnn)
%            Maximal formula atoms :    8 (   6 avg)
%            Number of connectives :   14 (   0   ~;   0   |;   0   &;  14   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   7 avg;  14 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :    2 (   2   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   4 usr;   4 con; 0-0 aty)
%            Number of variables   :    2 (   0   ^   2   !;   0   ?;   2   :)
% SPC      : 

% Comments : Requires LCL008^0.ax SWV008^0.ax
%          : THF0 syntax
%------------------------------------------------------------------------------
%----We add the reflexivity and the transitivity axiom to obtain S4.
thf(refl_axiom,axiom,
    ! [A: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ rel @ A ) @ A ) ) ).

thf(trans_axiom,axiom,
    ! [B: $i > $o] : ( mvalid @ ( mimpl @ ( mbox @ rel @ B ) @ ( mbox @ rel @ ( mbox @ rel @ B ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV008^2.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV008^2 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Software Verification (Security)
% Axioms   : ICL^=> logic based upon modal logic
% Version  : [Ben08] axioms.
% English  :

% Refs     : [GA08]  Garg & Abadi (2008), A Modal Deconstruction of Access
%          : [Ben08] Benzmueller (2008), Automating Access Control Logics i
%          : [BP09]  Benzmueller & Paulson (2009), Exploring Properties of
% Source   : [Ben08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   1 unt;   1 typ;   1 def)
%            Number of atoms       :    5 (   1 equ;   0 cnn)
%            Maximal formula atoms :    1 (   2 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   0   &;   4   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg;   4 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :    7 (   7   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    5 (   4 usr;   3 con; 0-3 aty)
%            Number of variables   :    2 (   2   ^   0   !;   0   ?;   2   :)
% SPC      : 

% Comments : Requires LCL008^0.ax SWV008^0.ax
%          : THF0 syntax
%------------------------------------------------------------------------------
%----The new connective 'speaks for'
thf(icl_impl_princ_type,type,
    icl_impl_princ: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(icl_impl_princ,definition,
    ( icl_impl_princ
    = ( ^ [A: $i > $o,B: $i > $o] : ( mbox @ rel @ ( mimpl @ A @ B ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV009+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV009+0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Software Verification
% Axioms   : General axioms for access to classified information
% Version  : [Gar09] axioms.
% English  :

% Refs     : [Gar09] Garg (2006), Email to G. Sutcliffe
% Source   : [Gar09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   41 (  12 unt;   0 def)
%            Number of atoms       :  129 (   0 equ)
%            Maximal formula atoms :   11 (   3 avg)
%            Number of connectives :   88 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;  88  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   16 (   6 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   55 (  55 usr;   0 prp; 1-6 aty)
%            Number of functors    :   14 (  14 usr;  13 con; 0-2 aty)
%            Number of variables   :  129 ( 129   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(ax0,axiom,
    ! [K] : loca_level_direct_below(K,unclassified,sbu) ).

fof(ax1,axiom,
    ! [K] : loca_level_direct_below(K,sbu,confidential) ).

fof(ax2,axiom,
    ! [K] : loca_level_direct_below(K,confidential,secret) ).

fof(ax3,axiom,
    ! [K] : loca_level_direct_below(K,secret,topsecret) ).

fof(ax4,axiom,
    ! [K,L] : loca_level_below(K,L,L) ).

fof(ax5,axiom,
    ! [K,L,L1,L11] :
      ( loca_level_direct_below(K,L1,L11)
     => ( loca_level_below(K,L,L1)
       => loca_level_below(K,L,L11) ) ) ).

fof(ax6,axiom,
    ! [C,SSO] :
      ( system_compartment_has_sso(system,C,SSO)
     => admin_compartment_has_sso(admin,C,SSO) ) ).

fof(ax7,axiom,
    ! [OCA,C,SSO,SCG] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_has_scg(OCA,C,SCG)
       => ( admin_compartment_has_sso(admin,C,SSO)
         => ( sso_compartment_has_scg(SSO,C,SCG)
           => admin_compartment_has_scg(admin,C,SCG) ) ) ) ) ).

fof(ax8,axiom,
    ! [F,CL] :
      ( system_file_needs_compartments(system,F,CL)
     => ( admin_file_has_compartments_h(admin,F,CL,CL)
       => admin_file_has_compartments(admin,F,CL) ) ) ).

fof(ax9,axiom,
    ! [F,CL] : admin_file_has_compartments_h(admin,F,CL,nil) ).

fof(ax10,axiom,
    ! [F,CL,C1,CL1,SSO] :
      ( admin_compartment_has_sso(admin,C1,SSO)
     => ( sso_file_has_compartments(SSO,F,CL)
       => ( admin_file_has_compartments_h(admin,F,CL,CL1)
         => admin_file_has_compartments_h(admin,F,CL,cons(C1,CL1)) ) ) ) ).

fof(ax11,axiom,
    ! [F,L,CL] :
      ( system_file_needs_level(system,F,L)
     => ( admin_file_has_compartments(admin,F,CL)
       => ( admin_file_has_level_h(admin,F,L,CL)
         => admin_file_has_level(admin,F,L) ) ) ) ).

fof(ax12,axiom,
    ! [F,L] : admin_file_has_level_h(admin,F,L,nil) ).

fof(ax13,axiom,
    ! [F,L,C,CL,SSO,SCG] :
      ( admin_compartment_has_sso(admin,C,SSO)
     => ( admin_compartment_has_scg(admin,C,SCG)
       => ( sso_file_has_level(SSO,F,L,SCG)
         => ( admin_file_has_level_h(admin,F,L,CL)
           => admin_file_has_level_h(admin,F,L,cons(C,CL)) ) ) ) ) ).

fof(ax14,axiom,
    ! [F,U,CL] :
      ( system_file_needs_citizenship(system,F,U)
     => ( admin_file_has_compartments(admin,F,CL)
       => ( admin_file_has_citizenship_h(admin,F,U,CL)
         => admin_file_has_citizenship(admin,F,U) ) ) ) ).

fof(ax15,axiom,
    ! [F,U] : admin_file_has_citizenship_h(admin,F,U,nil) ).

fof(ax16,axiom,
    ! [F,U,C,CL,SSO,SCG] :
      ( admin_compartment_has_sso(admin,C,SSO)
     => ( admin_compartment_has_scg(admin,C,SCG)
       => ( sso_file_has_citizenship(SSO,F,U,SCG)
         => ( admin_file_has_citizenship_h(admin,F,U,CL)
           => admin_file_has_citizenship_h(admin,F,U,cons(C,CL)) ) ) ) ) ).

fof(ax17,axiom,
    ! [K,PA] :
      ( system_indi_is_polygraph_admin(system,PA)
     => ( polygraph_admin_indi_has_polygraph(PA,K)
       => admin_indi_has_polygraph(admin,K) ) ) ).

fof(ax18,axiom,
    ! [K,CA] :
      ( system_indi_is_credit_admin(system,CA)
     => ( credit_admin_indi_has_credit(CA,K)
       => admin_indi_has_credit(admin,K) ) ) ).

fof(ax19,axiom,
    ! [K] : admin_indi_has_background(admin,K,unclassified) ).

fof(ax20,axiom,
    ! [K,L,BA,L1] :
      ( system_indi_is_background_admin(system,BA)
     => ( background_admin_indi_has_background(BA,K,L1)
       => ( loca_level_below(admin,L,L1)
         => admin_indi_has_background(admin,K,L) ) ) ) ).

fof(ax21,axiom,
    ! [K,HR] :
      ( system_indi_is_hr_admin(system,HR)
     => ( hr_admin_indi_has_employment(HR,K)
       => admin_indi_has_employment(admin,K) ) ) ).

fof(ax22,axiom,
    ! [K] : admin_indi_has_citizenship(admin,K,anycountry) ).

fof(ax23,axiom,
    ! [K,U] :
      ( system_indi_has_citizenship(system,K,U)
     => admin_indi_has_citizenship(admin,K,U) ) ).

fof(ax24,axiom,
    ! [K] : admin_indi_has_level(admin,K,unclassified) ).

fof(ax25,axiom,
    ! [K,L,L1,LA,L11] :
      ( system_indi_needs_level(system,K,L1)
     => ( admin_indi_has_citizenship(admin,K,usa)
       => ( admin_indi_has_polygraph(admin,K)
         => ( admin_indi_has_employment(admin,K)
           => ( admin_indi_has_credit(admin,K)
             => ( loca_level_below(admin,L,L1)
               => ( system_indi_is_level_admin(system,LA)
                 => ( level_admin_indi_has_level(LA,K,L11)
                   => ( loca_level_below(admin,L,L11)
                     => ( admin_indi_has_background(admin,K,L)
                       => admin_indi_has_level(admin,K,L) ) ) ) ) ) ) ) ) ) ) ).

fof(ax26,axiom,
    ! [K] : admin_indi_has_compartments(admin,K,nil) ).

fof(ax27,axiom,
    ! [K,C,CL,SSO] :
      ( system_indi_needs_compartment(system,K,C)
     => ( admin_indi_has_employment(admin,K)
       => ( admin_indi_has_citizenship(admin,K,usa)
         => ( admin_indi_has_polygraph_for_compartment(admin,K,C)
           => ( admin_indi_has_credit_for_compartment(admin,K,C)
             => ( admin_compartment_has_sso(admin,C,SSO)
               => ( sso_indi_has_compartment(SSO,K,C)
                 => ( admin_indi_has_background_for_compartment(admin,K,C)
                   => ( admin_indi_has_level_for_compartment(admin,K,C)
                     => ( admin_indi_has_compartments(admin,K,CL)
                       => admin_indi_has_compartments(admin,K,cons(C,CL)) ) ) ) ) ) ) ) ) ) ) ).

fof(ax28,axiom,
    ! [K,C,OCA,L1,L2,B1,B2] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,B1,B2)
       => ( admin_indi_has_background(admin,K,L2)
         => admin_indi_has_background_for_compartment(admin,K,C) ) ) ) ).

fof(ax29,axiom,
    ! [K,C,OCA,L1,L2,B1,B2] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,B1,B2)
       => ( admin_indi_has_level(admin,K,L1)
         => admin_indi_has_level_for_compartment(admin,K,C) ) ) ) ).

fof(ax30,axiom,
    ! [K,C,OCA,L1,L2,B1] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,B1,yes)
       => ( admin_indi_has_polygraph(admin,K)
         => admin_indi_has_polygraph_for_compartment(admin,K,C) ) ) ) ).

fof(ax31,axiom,
    ! [K,C,OCA,L1,L2,B1] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,B1,no)
       => admin_indi_has_polygraph_for_compartment(admin,K,C) ) ) ).

fof(ax32,axiom,
    ! [K,C,OCA,L1,L2,B2] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,yes,B2)
       => ( admin_indi_has_credit(admin,K)
         => admin_indi_has_credit_for_compartment(admin,K,C) ) ) ) ).

fof(ax33,axiom,
    ! [K,C,OCA,L1,L2,B2] :
      ( system_indi_is_oca(system,OCA)
     => ( oca_compartment_is_compartment(OCA,C,L1,L2,no,B2)
       => admin_indi_has_credit_for_compartment(admin,K,C) ) ) ).

fof(ax34,axiom,
    ! [K,F,CL] :
      ( admin_file_has_compartments(admin,F,CL)
     => ( admin_indi_has_compartments(admin,K,CL)
       => admin_indi_has_compartments_for_file(admin,K,F) ) ) ).

fof(ax35,axiom,
    ! [K,F,L] :
      ( admin_file_has_level(admin,F,L)
     => ( admin_indi_has_level(admin,K,L)
       => admin_indi_has_level_for_file(admin,K,F) ) ) ).

fof(ax36,axiom,
    ! [K,F,OWR] :
      ( state_file_has_owner(F,OWR)
     => ( owner_indi_has_need_to_know(OWR,K,F)
       => admin_indi_has_need_to_know_for_file(admin,K,F) ) ) ).

fof(ax37,axiom,
    ! [K,F,L] :
      ( admin_file_has_citizenship(admin,F,L)
     => ( admin_indi_has_citizenship(admin,K,L)
       => admin_indi_has_citizenship_for_file(admin,K,F) ) ) ).

fof(ax38,axiom,
    ! [K,F] :
      ( admin_indi_has_citizenship(admin,K,usa)
     => admin_indi_has_citizenship_for_file(admin,K,F) ) ).

fof(ax39,axiom,
    ! [K,F] :
      ( state_file_is_not_working_paper(F)
     => ( admin_indi_has_citizenship_for_file(admin,K,F)
       => ( admin_indi_has_need_to_know_for_file(admin,K,F)
         => ( admin_indi_has_level_for_file(admin,K,F)
           => ( admin_indi_has_compartments_for_file(admin,K,F)
             => admin_indi_may_file(admin,K,F,read) ) ) ) ) ) ).

fof(ax40,axiom,
    ! [K,F,K1] :
      ( state_file_has_owner(F,K1)
     => ( system_indi_is_counterintelligence(system,K,K1)
       => admin_indi_may_file(admin,K,F,read) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV010^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV010^0 : TPTP v8.2.0. Released v3.7.0.
% Domain   : Software Verification (Security)
% Axioms   : Translation from Binder Logic (BL) to CS4
% Version  : [Gar08] axioms.
% English  :

% Refs     : [AM+01] Alechina et al. (2001), Categorical and Kripke Semanti
%          : [Gar08] Garg (2008), Principal-Centric Reasoning in Constructi
%          : [Gar09] Garg (2009), Email to Geoff Sutcliffe
% Source   : [Gar09]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :   23 (  10 unt;  12 typ;  10 def)
%            Number of atoms       :   38 (  10 equ;   0 cnn)
%            Maximal formula atoms :    5 (   1 avg)
%            Number of connectives :   20 (   0   ~;   0   |;   0   &;  20   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   2 avg;  20 nst)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   46 (  46   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   24 (  23 usr;  12 con; 0-3 aty)
%            Number of variables   :   12 (  12   ^   0   !;   0   ?;  12   :)
% SPC      : 

% Comments : Requires LCL008^0.ax LCL009^0.ax
%          : This translation is not perfectly correct, because BL does not
%            admit the Barcan formula, but its translation to BM4 does. That
%            will not make a difference to the policies, however.
%          : THF0 syntax
%------------------------------------------------------------------------------
%----We now introduce one predicate for each connective of BL, and define the
%----predicates.
%----An injection from principals to formulas. Has no definition, it's symbolic.
thf(princ_inj,type,
    princ_inj: individuals > $i > $o ).

thf(bl_atom_decl,type,
    bl_atom: ( $i > $o ) > $i > $o ).

thf(bl_princ_decl,type,
    bl_princ: ( $i > $o ) > $i > $o ).

thf(bl_and_decl,type,
    bl_and: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(bl_or_decl,type,
    bl_or: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(bl_impl_decl,type,
    bl_impl: ( $i > $o ) > ( $i > $o ) > $i > $o ).

thf(bl_all_decl,type,
    bl_all: ( individuals > $i > $o ) > $i > $o ).

thf(bl_true_decl,type,
    bl_true: $i > $o ).

thf(bl_false_decl,type,
    bl_false: $i > $o ).

thf(bl_says_decl,type,
    bl_says: individuals > ( $i > $o ) > $i > $o ).

thf(bl_atom,definition,
    ( bl_atom
    = ( ^ [P: $i > $o] : ( cs4_atom @ P ) ) ) ).

thf(bl_princ,definition,
    ( bl_princ
    = ( ^ [P: $i > $o] : ( cs4_atom @ P ) ) ) ).

thf(bl_and,definition,
    ( bl_and
    = ( ^ [A: $i > $o,B: $i > $o] : ( cs4_and @ A @ B ) ) ) ).

thf(bl_or,definition,
    ( bl_or
    = ( ^ [A: $i > $o,B: $i > $o] : ( cs4_or @ A @ B ) ) ) ).

thf(bl_impl,definition,
    ( bl_impl
    = ( ^ [A: $i > $o,B: $i > $o] : ( cs4_impl @ A @ B ) ) ) ).

thf(bl_all,definition,
    ( bl_all
    = ( ^ [A: individuals > $i > $o] : ( cs4_all @ A ) ) ) ).

thf(bl_true,definition,
    bl_true = cs4_true ).

thf(bl_false,definition,
    bl_false = cs4_false ).

thf(bl_says,definition,
    ( bl_says
    = ( ^ [K: individuals,A: $i > $o] : ( cs4_box @ ( cs4_impl @ ( bl_princ @ ( princ_inj @ K ) ) @ A ) ) ) ) ).

%----Validity in BL
thf(bl_valid_decl,type,
    bl_valid: ( $i > $o ) > $o ).

thf(bl_valid_def,definition,
    bl_valid = mvalid ).

%----Local authority (loca) - the strongest principal.
thf(loca_decl,type,
    loca: individuals ).

%----Every principal must entail loca, this makes loca the strongest principal.
%----This is done by adding the CS4 axiom: forall K. [] (K => loca).
thf(loca_strength,axiom,
    ( cs4_valid
    @ ( cs4_all
      @ ^ [K: individuals] : ( cs4_impl @ ( princ_inj @ K ) @ ( princ_inj @ loca ) ) ) ) ).

%------------------------------------------------------------------------------

```

### ./SWV011+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV011+0 : TPTP v8.2.0. Released v4.0.0.
% Domain   : Software Verification
% Axioms   : Axioms for verification of Stoller's leader election algorithm
% Version  : [Sve07] axioms : Especial.
% English  :

% Refs     : [Sto97] Stoller (1997), Leader Election in Distributed Systems
%          : [Sve07] Svensson (2007), Email to Koen Claessen
%          : [Sve08] Svensson (2008), A Semi-Automatic Correctness Proof Pr
% Source   : [Sve07]
% Names    : stoller2 [Sve07]
%          : con_sys [Sve07]
%          : cons_snoc [Sve07]
%          : arith [Sve07]
%          : sets [Sve07]

% Status   : Satisfiable
% Syntax   : Number of formulae    :   66 (  40 unt;   0 def)
%            Number of atoms       :  111 (  62 equ)
%            Maximal formula atoms :    7 (   1 avg)
%            Number of connectives :   89 (  44   ~;   7   |;  14   &)
%                                         (  13 <=>;  11  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    6 (   5 usr;   0 prp; 1-2 aty)
%            Number of functors    :   27 (  27 usr;  11 con; 0-2 aty)
%            Number of variables   :  119 ( 118   !;   1   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Stoller axioms messages and such things
%----NewPid
fof(axiom,axiom,
    ! [Pid,Pid2] :
      ( elem(m_Ack(Pid,Pid2),queue(host(Pid)))
     => ( setIn(Pid,pids)
        & setIn(Pid2,pids) ) ) ).

fof(axiom_01,axiom,
    ! [P,Q] :
      ( s(host(P)) = host(Q)
     => host(P) != host(Q) ) ).

fof(axiom_02,axiom,
    ! [P] : leq(s(zero),host(P)) ).

fof(axiom_03,axiom,
    leq(s(zero),nbr_proc) ).

fof(axiom_04,axiom,
    ! [P] : leq(host(P),nbr_proc) ).

fof(axiom_05,axiom,
    elec_1 != elec_2 ).

fof(axiom_06,axiom,
    elec_1 != wait ).

fof(axiom_07,axiom,
    elec_1 != norm ).

fof(axiom_08,axiom,
    elec_2 != wait ).

fof(axiom_09,axiom,
    elec_2 != norm ).

fof(axiom_10,axiom,
    norm != wait ).

fof(axiom_11,axiom,
    ! [X,Y,Z] : m_Ack(X,Y) != m_Halt(Z) ).

fof(axiom_12,axiom,
    ! [X,Y,Z] : m_Ack(X,Y) != m_Down(Z) ).

fof(axiom_13,axiom,
    ! [X,Y,Z] : m_Ack(X,Y) != m_NotNorm(Z) ).

fof(axiom_14,axiom,
    ! [X,Y,Z] : m_Ack(X,Y) != m_Ldr(Z) ).

fof(axiom_15,axiom,
    ! [X,Y,Z] : m_Ack(X,Y) != m_NormQ(Z) ).

fof(axiom_16,axiom,
    ! [X,Y] : m_NotNorm(X) != m_Halt(Y) ).

fof(axiom_17,axiom,
    ! [X,Y] : m_Down(X) != m_Halt(Y) ).

fof(axiom_18,axiom,
    ! [X,Y] : m_Down(X) != m_Ldr(Y) ).

fof(axiom_19,axiom,
    ! [X,Y] : m_Down(X) != m_NotNorm(Y) ).

fof(axiom_20,axiom,
    ! [X,Y] : m_Down(X) != m_NormQ(Y) ).

fof(axiom_21,axiom,
    ! [X,Y] : m_NormQ(X) != m_Halt(Y) ).

fof(axiom_22,axiom,
    ! [X,Y] : m_Ldr(X) != m_Halt(Y) ).

fof(axiom_23,axiom,
    ! [X,Y] : m_Ldr(X) != m_NormQ(Y) ).

fof(axiom_24,axiom,
    ! [X,Y] : m_Ldr(X) != m_NotNorm(Y) ).

fof(axiom_25,axiom,
    ! [X,Y] : m_NormQ(X) != m_NotNorm(Y) ).

fof(axiom_26,axiom,
    ! [X,Y] :
      ( X != Y
    <=> m_Halt(X) != m_Halt(Y) ) ).

fof(axiom_27,axiom,
    ! [X,Y] :
      ( X != Y
    <=> m_NormQ(X) != m_NormQ(Y) ) ).

fof(axiom_28,axiom,
    ! [X,Y] :
      ( X != Y
    <=> m_NotNorm(X) != m_NotNorm(Y) ) ).

fof(axiom_29,axiom,
    ! [X,Y] :
      ( X != Y
    <=> m_Ldr(X) != m_Ldr(Y) ) ).

fof(axiom_30,axiom,
    ! [X,Y] :
      ( X != Y
    <=> m_Down(X) != m_Down(Y) ) ).

fof(axiom_31,axiom,
    ! [X1,X2,Y1,Y2] :
      ( X1 != X2
     => m_Ack(X1,Y1) != m_Ack(X2,Y2) ) ).

fof(axiom_32,axiom,
    ! [X1,X2,Y1,Y2] :
      ( Y1 != Y2
     => m_Ack(X1,Y1) != m_Ack(X2,Y2) ) ).

%----Axioms for a concurrent system; i.e. Pids and Alive
fof(axiom_33,axiom,
    ! [Pid,Pid2] :
      ( host(Pid) != host(Pid2)
     => Pid != Pid2 ) ).

fof(axiom_34,axiom,
    ~ setIn(nil,alive) ).

%----Axioms for snoc and cons style of queues
%----Injective
fof(axiom_35,axiom,
    ! [X,Q] : head(cons(X,Q)) = X ).

fof(axiom_36,axiom,
    ! [X,Q] : tail(cons(X,Q)) = Q ).

fof(axiom_37,axiom,
    ! [Y,Q] : last(snoc(Q,Y)) = Y ).

fof(axiom_38,axiom,
    ! [Y,Q] : init(snoc(Q,Y)) = Q ).

%----Surjective
fof(axiom_39,axiom,
    ! [Q] :
      ( Q = q_nil
      | Q = cons(head(Q),tail(Q)) ) ).

fof(axiom_40,axiom,
    ! [Q] :
      ( Q = q_nil
      | Q = snoc(init(Q),last(Q)) ) ).

%----Exclusive
fof(axiom_41,axiom,
    ! [X,Q] : q_nil != cons(X,Q) ).

fof(axiom_42,axiom,
    ! [Y,Q] : q_nil != snoc(Q,Y) ).

%----Equal singleton queue
fof(axiom_43,axiom,
    ! [X] : cons(X,q_nil) = snoc(q_nil,X) ).

%----Snoc+cons equals cons+snoc
fof(axiom_44,axiom,
    ! [X,Y,Q] : snoc(cons(X,Q),Y) = cons(X,snoc(Q,Y)) ).

%----Elem
fof(axiom_45,axiom,
    ! [X] : ~ elem(X,q_nil) ).

fof(axiom_46,axiom,
    ! [X,Y,Q] :
      ( elem(X,cons(Y,Q))
    <=> ( X = Y
        | elem(X,Q) ) ) ).

fof(axiom_47,axiom,
    ! [X,Y,Q] :
      ( elem(X,snoc(Q,Y))
    <=> ( X = Y
        | elem(X,Q) ) ) ).

%----Ordered
fof(axiom_48,axiom,
    ! [X] :
      ( pidElem(X)
    <=> ? [Y] :
          ( X = m_Halt(Y)
          | X = m_Down(Y) ) ) ).

fof(axiom_49,axiom,
    ! [X] : pidMsg(m_Halt(X)) = X ).

fof(axiom_50,axiom,
    ! [X] : pidMsg(m_Down(X)) = X ).

fof(axiom_51,axiom,
    ordered(q_nil) ).

fof(axiom_52,axiom,
    ! [X] :
      ( ordered(cons(X,q_nil))
      & ordered(snoc(q_nil,X)) ) ).

fof(axiom_53,axiom,
    ! [X,Q] :
      ( ordered(cons(X,Q))
    <=> ( ordered(Q)
        & ! [Y] :
            ( ( elem(Y,Q)
              & pidElem(X)
              & pidElem(Y)
              & host(pidMsg(Y)) = host(pidMsg(X)) )
           => leq(pidMsg(X),pidMsg(Y)) ) ) ) ).

fof(axiom_54,axiom,
    ! [X,Q] :
      ( ordered(snoc(Q,X))
    <=> ( ordered(Q)
        & ! [Y] :
            ( ( elem(Y,Q)
              & pidElem(X)
              & pidElem(Y)
              & host(pidMsg(Y)) = host(pidMsg(X)) )
           => leq(pidMsg(Y),pidMsg(X)) ) ) ) ).

%----Helper axioms
fof(axiom_55,axiom,
    ! [Q,X,Y] :
      ( ordered(Q)
     => ordered(snoc(Q,m_Ack(X,Y))) ) ).

fof(axiom_56,axiom,
    ! [Q,X] :
      ( ordered(Q)
     => ordered(snoc(Q,m_Ldr(X))) ) ).

fof(axiom_57,axiom,
    ! [Q,X,Y] :
      ( ( ordered(cons(m_Halt(X),Q))
        & host(X) = host(Y)
        & elem(m_Down(Y),Q) )
     => leq(X,Y) ) ).

fof(axiom_58,axiom,
    ! [X] : ~ leq(s(X),X) ).

fof(axiom_59,axiom,
    ! [X] : leq(X,X) ).

fof(axiom_60,axiom,
    ! [X,Y] :
      ( leq(X,Y)
      | leq(Y,X) ) ).

fof(axiom_61,axiom,
    ! [X,Y] :
      ( ( leq(X,Y)
        & leq(Y,X) )
    <=> X = Y ) ).

fof(axiom_62,axiom,
    ! [X,Y,Z] :
      ( ( leq(X,Y)
        & leq(Y,Z) )
     => leq(X,Z) ) ).

fof(axiom_63,axiom,
    ! [X,Y] :
      ( leq(X,Y)
    <=> leq(s(X),s(Y)) ) ).

fof(axiom_64,axiom,
    ! [X,Y] :
      ( leq(X,s(Y))
    <=> ( X = s(Y)
        | leq(X,Y) ) ) ).

%----Set axioms
fof(axiom_65,axiom,
    ! [X] : ~ setIn(X,setEmpty) ).

%------------------------------------------------------------------------------

```

### ./SWV012+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV012+0 : TPTP v8.2.0. Released v5.2.0.
% Domain   : Software Verification
% Axioms   : Syntactic definitions of the logical operators 
% Version  : [deN09] axioms : Especial.
% English  :

% Refs     : [deN09] de Nivelle (2009), Email to Geoff Sutcliffe
% Source   : [deN09]
% Names    : 

% Status   : Satisfiable
% Syntax   : Number of formulae    :   44 (  14 unt;   0 def)
%            Number of atoms       :   96 (  49 equ)
%            Maximal formula atoms :    9 (   2 avg)
%            Number of connectives :   77 (  25   ~;   6   |;  26   &)
%                                         (   5 <=>;  15  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   10 (   4 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :   27 (  27 usr;   5 con; 0-3 aty)
%            Number of variables   :   75 (  61   !;  14   ?)
% SPC      : FOF_SAT_RFO_SEQ

% Comments : For each op in {and, lazy_and, or, exists, not, false}, this file
%            contains the following: 
%                op1 : the semantic definition of Theorem 4.
%                op2 : the syntactic definition of Figure 4. 
%            For each operator, we define a goal of form 
%                FOR EACH arg1, ... argn, 
%                    op1(arg1,...,argn) = op2(arg1, ..., argn).
%            We specify the structure of the domain U_D. 
%            We define the following predicates: 
%                d(A) :      A in D. 
%                bool(A) :   A in { false, true }.
%            Note that U_D = U_0 |_| U_1 |_| U_2 |_| ...., and D = U_0.
%------------------------------------------------------------------------------
%----The predicate bool is true exactly on true and false:
fof(def_bool,axiom,
    ! [X] :
      ( bool(X)
    <=> ( X = false
        | X = true ) ) ).

%----err, true and false are distinct constants:
fof(distinct_false_true_err,axiom,
    ( true != false
    & true != err
    & false != err ) ).

%----err, true and false are in D:
fof(false_true_err_in_d,axiom,
    ( d(true)
    & d(false)
    & d(err) ) ).

%----forallprefers is needed by the forall quantifier. 
%----In the rest of this comment we write '<' for 'forallprefers.'
%----< is defined by the sequence
%----( U_D \ D ) < ( D \ bool ) < f < t. 
%----The value of forall x   p(x) is obtained as follows:
%----First define R := range of   lambda x. p(x).
%----Select a <-minimal element in R.
%----Return Phi(r), where r is the selected element. 

%----Notin D is preferred over D.
%----Inside D, nonbool is preferred over bool.
%----Inside bool, false is preferred over true:
%----The <-order is partial.
fof(def_forallprefers,axiom,
    ! [X,Y] :
      ( forallprefers(X,Y)
    <=> ( ( ~ d(X)
          & d(Y) )
        | ( d(X)
          & d(Y)
          & ~ bool(X)
          & bool(Y) )
        | ( X = false
          & Y = true ) ) ) ).

%----existsprefers is like forallprefers, but it is defined by
%----the sequence: 
%---- ( U_D \ D ) < ( D \ bool ) < t < f. 
fof(def_existsprefers,axiom,
    ! [X,Y] :
      ( existsprefers(X,Y)
    <=> ( ( ~ d(X)
          & d(Y) )
        | ( d(X)
          & d(Y)
          & ~ bool(X)
          & bool(Y) )
        | ( X = true
          & Y = false ) ) ) ).

%----The function phi(X) is defined by:
%----phi(X) = err if X not in D.
%----phi(X) = X if X in D.
%----It is defined in Definition 8 of the paper. 
fof(def_phi,axiom,
    ! [X] :
      ( ( d(X)
        & phi(X) = X )
      | ( ~ d(X)
        & phi(X) = err ) ) ).

%----Axiomatization of prop. 
%----The difference between bool and prop is that bool
%----is a predicate which we use in the meta language (TPTP),
%----while prop is a function inside the logic.
fof(prop_true,axiom,
    ! [X] :
      ( prop(X) = true
    <=> bool(X) ) ).

fof(prop_false,axiom,
    ! [X] :
      ( prop(X) = false
    <=> ~ bool(X) ) ).

%----Axiomatization of impl. Because impl and lazy_impl are primitive,
%----they have only one definition: 
%----   If A is not bool, then ( A -> B ) = phi(A). 
%----   If A is bool, but B is not bool, then ( A -> B ) = phi(B). 
%----   If A is false, and B is bool, then ( A -> B ) = true
%----   If A is true, and B is bool, then ( A -> B ) = B. 
fof(impl_axiom1,axiom,
    ! [A,B] :
      ( ~ bool(A)
     => impl(A,B) = phi(A) ) ).

fof(impl_axiom2,axiom,
    ! [A,B] :
      ( ( bool(A)
        & ~ bool(B) )
     => impl(A,B) = phi(B) ) ).

fof(impl_axiom3,axiom,
    ! [B] :
      ( bool(B)
     => impl(false,B) = true ) ).

fof(impl_axiom4,axiom,
    ! [B] :
      ( bool(B)
     => impl(true,B) = B ) ).

%----Axiomatization of lazy_impl:
%----   If A is not bool, then [A] B = phi(A). 
%----   If A is false, then [A] B = true. 
%----   If A is true, then [A] B = phi(B). 
fof(lazy_impl_axiom1,axiom,
    ! [A,B] :
      ( ~ bool(A)
     => lazy_impl(A,B) = phi(A) ) ).

fof(lazy_impl_axiom2,axiom,
    ! [B] : lazy_impl(false,B) = true ).

fof(lazy_impl_axiom3,axiom,
    ! [B] : lazy_impl(true,B) = phi(B) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----Axiomatization of semantic definition of and:
%----   If A is not bool, then ( A /\ B ) = phi(A). 
%----   If A is bool, but B is not bool, then ( A /\ B ) = phi(B). 
%----   If A = false, and B is bool, then ( A /\ B ) = false.
%----   If A = true, and B is bool, then ( A /\ B ) = B.
fof(and1_axiom1,axiom,
    ! [A,B] :
      ( ~ bool(A)
     => and1(A,B) = phi(A) ) ).

fof(and1_axiom2,axiom,
    ! [A,B] :
      ( ( bool(A)
        & ~ bool(B) )
     => and1(A,B) = phi(B) ) ).

fof(and1_axiom3,axiom,
    ! [B] :
      ( bool(B)
     => and1(false,B) = false ) ).

fof(and1_axiom4,axiom,
    ! [B] :
      ( bool(B)
     => and1(true,B) = B ) ).

%----Syntactic definition of and in Figure 4:
%----The definition is:
%----P /\ Q = forall R, [ Prop(R) ] ( P -> Q -> R ) -> R.
fof(def_f1,axiom,
    ! [P,Q,R] : f1(P,Q,R) = lazy_impl(prop(R),impl(impl(P,impl(Q,R)),R)) ).

fof(def_and2,axiom,
    ! [P,Q] :
    ? [R] :
      ( and2(P,Q) = phi(f1(P,Q,R))
      & ~ ? [R1] : forallprefers(f1(P,Q,R1),f1(P,Q,R)) ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----Axiomatization of semantic definition of lazy_and:
%----   If A is not bool, then <A> B = phi(A). 
%----   If A is false, then <A> B = false. 
%----   If A is true, then <A> B = phi(B). 
fof(lazy_and1_axiom1,axiom,
    ! [A,B] :
      ( ~ bool(A)
     => lazy_and1(A,B) = phi(A) ) ).

fof(lazy_and1_axiom2,axiom,
    ! [B] : lazy_and1(false,B) = false ).

fof(lazy_and1_axiom3,axiom,
    ! [B] : lazy_and1(true,B) = phi(B) ).

%----Syntactic definition of lazy_and in Figure 4:
%----The definition is:
%----   <P> Q = forall R, [ Prop(R) ] ( [ P ] Q -> R ) -> R.
fof(def_f2,axiom,
    ! [P,Q,R] : f2(P,Q,R) = lazy_impl(prop(R),impl(lazy_impl(P,impl(Q,R)),R)) ).

fof(def_lazy_and2,axiom,
    ! [P,Q] :
    ? [R] :
      ( lazy_and2(P,Q) = phi(f2(P,Q,R))
      & ~ ? [R1] : forallprefers(f2(P,Q,R1),f2(P,Q,R)) ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----Axiomatization of semantic definition of or: 
%----   If A is not bool, then ( A \/ B ) = phi(A).
%----   If A is bool, but B is not bool, then ( A \/ B ) = phi(B).
%----   If A = true, and B is bool, then ( A \/ B ) = true.
%----   If A = false, and B is bool, then ( A \/ B ) = B.
fof(or1_axiom1,axiom,
    ! [A,B] :
      ( ~ bool(A)
     => or1(A,B) = phi(A) ) ).

fof(or1_axiom2,axiom,
    ! [A,B] :
      ( ( bool(A)
        & ~ bool(B) )
     => or1(A,B) = phi(B) ) ).

fof(or1_axiom3,axiom,
    ! [B] :
      ( bool(B)
     => or1(true,B) = true ) ).

fof(or1_axiom4,axiom,
    ! [B] :
      ( bool(B)
     => or1(false,B) = B ) ).

%----Syntactic definition of or in Figure 4.
%----The definition is:
%----P \/ Q = forall R, [ Prop(R) ] ( P -> R ) -> ( Q -> R ) -> R.
fof(def_f3,axiom,
    ! [P,Q,R] : f3(P,Q,R) = lazy_impl(prop(R),impl(impl(P,R),impl(impl(Q,R),R))) ).

fof(def_or2,axiom,
    ! [P,Q] :
    ? [R] :
      ( or2(P,Q) = phi(f3(P,Q,R))
      & ~ ? [R1] : forallprefers(f3(P,Q,R1),f3(P,Q,R)) ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----Axiomatization of semantic definition of exists. 
%----
%----For each predicate, there exists an an x, s.t.
%----exists(P) = phi( P. x ) and 
%----   there exists no x1, s.t. ( P. x1 ) < ( P. x ), where 
%----      < is the existsprefers order, and 
%----      . is the application operator. 
fof(exists1_axiom1,axiom,
    ! [P] :
    ? [X] :
      ( exists1(P) = phi(apply(P,X))
      & ~ ? [X1] : existsprefers(apply(P,X1),apply(P,X)) ) ).

%----Syntactic definition of exists in the paper:
%
%----( Exists P ) = forall R, [ Prop(R) ] ( forall x ( P x ) -> R ) -> R.
%
%----We define functions  f4(P,x,R) :=   ( P. x ) -> R.
%----                     f5(P,R)   :=   forall x. f4( P,x,R )
%----                     f6(P,R)   :=   [ Prop(R) ] f5( P, R ) -> R. 
%----                     exists2(P) :=  forall R. f6( P, R ).  
fof(def_f4,axiom,
    ! [P,X,R] : f4(P,X,R) = impl(apply(P,X),R) ).

fof(def_f5,axiom,
    ! [P,R] :
    ? [X] :
      ( f5(P,R) = phi(f4(P,X,R))
      & ~ ? [X1] : forallprefers(f4(P,X1,R),f4(P,X,R)) ) ).

fof(def_f6,axiom,
    ! [P,R] : f6(P,R) = lazy_impl(prop(R),impl(f5(P,R),R)) ).

fof(def_exists2,axiom,
    ! [P] :
    ? [R] :
      ( exists2(P) = phi(f6(P,R))
      & ~ ? [R1] : forallprefers(f6(P,R1),f6(P,R)) ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----The semantic definition of false is just the false constant.
fof(def_false1,axiom,
    false1 = false ).

%----The syntactic definition of false equals: 
%----   false := forall P, [ Prop(P) ] P .
%----f7(P) := [ Prop(P) ] P.
fof(def_f7,axiom,
    ! [P] : f7(P) = lazy_impl(prop(P),P) ).

fof(def_false2,axiom,
    ? [P] :
      ( false2 = phi(f7(P))
      & ~ ? [P1] : forallprefers(f7(P1),f7(P)) ) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%----Axiomatization of semantic definition of not: 
%----   If A is not bool, then not(A) = phi(A). 
%----   If A = false, then not(A) = true. 
%----   If A = true, then not(A) = false. 
fof(not1_axiom1,axiom,
    ! [A] :
      ( ~ bool(A)
     => not1(A) = phi(A) ) ).

fof(not1_axiom2,axiom,
    not1(false) = true ).

fof(not1_axiom3,axiom,
    not1(true) = false ).

%----Syntactic definition of not in paper:
%----The definition is:
%----~ P := ( P -> False ).
fof(def_not2,axiom,
    ! [P] : not2(P) = impl(P,false2) ).

%------------------------------------------------------------------------------

```

### ./SWV013-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SWV013-0 : TPTP v8.2.0. Released v5.2.0.
% Domain   : Software Verification
% Axioms   : Lists in Separation Logic
% Version  : [Nav11] axioms.
% English  : Axioms for proving entailments between separation logic formulas
%            with list predicates.

% Refs     : [BCO05] Berdine et al. (2005), Symbolic Execution with Separat
%          : [RN11]  Rybalchenko & Navarro Perez (2011), Separation Logic +
%          : [Nav11] Navarro Perez (2011), Email to Geoff Sutcliffe
% Source   : [Nav11]
% Names    : SepLogicLists [Nav11]

% Status   : Satisfiable
% Syntax   : Number of clauses     :   11 (   4 unt;   3 nHn;   9 RR)
%            Number of literals    :   21 (   8 equ;   9 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   38 (   9 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----S * T * Sigma = T * S * Sigma.
cnf(associative_commutative,axiom,
    sep(S,sep(T,Sigma)) = sep(T,sep(S,Sigma)) ).

%----lseg(X, X) * Sigma = Sigma.
cnf(normalization,axiom,
    sep(lseg(X,X),Sigma) = Sigma ).

%----next(nil, Y) * Sigma --> bot.
cnf(wellformedness_1,axiom,
    ~ heap(sep(next(nil,Y),Sigma)) ).

%----lseg(nil, Y) * Sigma --> Y = nil.
cnf(wellformedness_2,axiom,
    ( ~ heap(sep(lseg(nil,Y),Sigma))
    | Y = nil ) ).

%----next(X, Y) * next(X, Z) * Sigma --> bot.
cnf(wellformedness_3,axiom,
    ~ heap(sep(next(X,Y),sep(next(X,Z),Sigma))) ).

%----next(X, Y) * lseg(X, Z) * Sigma --> X = Z.
cnf(wellformedness_4,axiom,
    ( ~ heap(sep(next(X,Y),sep(lseg(X,Z),Sigma)))
    | X = Z ) ).

%----lseg(X, Y) * lseg(X, Z) * Sigma --> X = Y, X = Z.
cnf(wellformedness_5,axiom,
    ( ~ heap(sep(lseg(X,Y),sep(lseg(X,Z),Sigma)))
    | X = Y
    | X = Z ) ).

%----next(X, Z) * Sigma --> X = Z, lseg(X, Z) * Sigma. (REDUNDANT: U2 + NORM)
%cnf(unfolding_1,axiom,
%   ( ~ heap(sep(next(X, Z), Sigma))
%   | X = Z
%   | heap(sep(lseg(X, Z), Sigma)) )).

%----next(X, Y) * lseg(Y, Z) * Sigma --> X = Y, lseg(X, Z) * Sigma.
cnf(unfolding_2,axiom,
    ( ~ heap(sep(next(X,Y),sep(lseg(Y,Z),Sigma)))
    | X = Y
    | heap(sep(lseg(X,Z),Sigma)) ) ).

%----lseg(X, Y) * lseg(Y, nil) * Sigma --> lseg(X, nil) * Sigma.
cnf(unfolding_3,axiom,
    ( ~ heap(sep(lseg(X,Y),sep(lseg(Y,nil),Sigma)))
    | heap(sep(lseg(X,nil),Sigma)) ) ).

%----lseg(X, Y) * lseg(Y, Z) * next(Z, W) * Sigma --> 
%----    lseg(X, Z) * next(Z, W) * Sigma.
cnf(unfolding_4,axiom,
    ( ~ heap(sep(lseg(X,Y),sep(lseg(Y,Z),sep(next(Z,W),Sigma))))
    | heap(sep(lseg(X,Z),sep(next(Z,W),Sigma))) ) ).

%----lseg(X, Y) * lseg(Y, Z) * lseg(Z, W) * Sigma --> 
%----    Z = W, lseg(X, Z) * lseg(Z, W) * Sigma.
cnf(unfolding_5,axiom,
    ( ~ heap(sep(lseg(X,Y),sep(lseg(Y,Z),sep(lseg(Z,W),Sigma))))
    | Z = W
    | heap(sep(lseg(X,Z),sep(lseg(Z,W),Sigma))) ) ).

%------------------------------------------------------------------------------

```

### ./SYN000+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SYN000+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Syntactic
% Axioms   : A simple include file for FOF
% Version  : Biased.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    3 (   3 unt;   0 def)
%            Number of atoms       :    3 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    3 (   3 usr;   3 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Some axioms to include
fof(ia1,axiom,
    ia1 ).

fof(ia2,axiom,
    ia2 ).

fof(ia3,axiom,
    ia3 ).

%------------------------------------------------------------------------------

```

### ./SYN000-0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SYN000-0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Syntactic
% Axioms   : A simple include file for CNF
% Version  : Biased.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   3 RR)
%            Number of literals    :    3 (   0 equ;   0 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    3 (   3 usr;   3 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Some axioms to include
cnf(ia1,axiom,
    ia1 ).

cnf(ia2,axiom,
    ia2 ).

cnf(ia3,axiom,
    ia3 ).

%------------------------------------------------------------------------------

```

### ./SYN000^0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SYN000^0 : TPTP v8.2.0. Released v3.7.0.
% Domain   : Syntactic
% Axioms   : A simple include file for THF
% Version  : Biased.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   3 unt;   3 typ;   0 def)
%            Number of atoms       :    3 (   0 equ;   0 cnn)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &;   0   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Number of types       :    1 (   0 usr)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   3 usr;   3 con; 0-0 aty)
%            Number of variables   :    0 (   0   ^   0   !;   0   ?;   0   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Some axioms to include
thf(ia1_type,type,
    ia1: $o ).

thf(ia2_type,type,
    ia2: $o ).

thf(ia3_type,type,
    ia3: $o ).

thf(ia1,axiom,
    ia1 ).

thf(ia2,axiom,
    ia2 ).

thf(ia3,axiom,
    ia3 ).

%------------------------------------------------------------------------------

```

### ./SYN000_0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SYN000_0 : TPTP v8.2.0. Released v5.0.0.
% Domain   : Syntactic
% Axioms   : A simple include file for TFF
% Version  : Biased.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    6 (   3 unt;   3 typ;   0 def)
%            Number of atoms       :    3 (   0 equ)
%            Maximal formula atoms :    1 (   0 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    1 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of types       :    1 (   0 usr)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    3 (   3 usr;   3 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0   !;   0   ?;   0   :)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
%----Some axioms to include
tff(ia1_type,type,
    ia1: $o ).

tff(ia2_type,type,
    ia2: $o ).

tff(ia3_type,type,
    ia3: $o ).

tff(ia1,axiom,
    ia1 ).

tff(ia2,axiom,
    ia2 ).

tff(ia3,axiom,
    ia3 ).

%------------------------------------------------------------------------------

```

### ./SYN001-0.ax

Very long 1821

### ./SYN002+0.ax

```vampire
%------------------------------------------------------------------------------
% File     : SYN002+0 : TPTP v8.2.0. Released v3.6.0.
% Domain   : Syntactic
% Axioms   : Orevkov formula
% Version  : [TS00] axioms : Especial.
% English  : r(x,y,z)=y+2^x=z

% Refs     : [TS00]  Troelska & Schwichtenberg (2000), Basic Proof Theory
%          : [Rat08] Raths (2008), Email to G. Sutcliffe
% Source   : [Rat08]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of formulae    :    2 (   1 unt;   0 def)
%            Number of atoms       :    4 (   0 equ)
%            Maximal formula atoms :    3 (   2 avg)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :    5 (   5   !;   0   ?)
% SPC      : 

% Comments :
%------------------------------------------------------------------------------
fof(hyp1,axiom,
    ! [Y] : r(Y,zero,succ(Y)) ).

fof(hyp2,axiom,
    ! [Y,X,Z,Z1] :
      ( r(Y,X,Z)
     => ( r(Z,X,Z1)
       => r(Y,succ(X),Z1) ) ) ).

%------------------------------------------------------------------------------

```

### ./TOP001-0.ax

```vampire
%--------------------------------------------------------------------------
% File     : TOP001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Topology (Point set)
% Axioms   : Point-set topology
% Version  : [WM89] axioms : Incomplete.
% English  :

% Refs     : [WM89]  Wick & McCune (1989), Automated Reasoning about Elemen
% Source   : [WM89]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :  109 (   0 unt;  23 nHn; 104 RR)
%            Number of literals    :  336 (   0 equ; 205 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :   22 (  22 usr;   0 prp; 1-4 aty)
%            Number of functors    :   35 (  35 usr;   1 con; 0-5 aty)
%            Number of variables   :  357 (  56 sgn)
% SPC      : 

% Comments : These axioms are incomplete, in that they do not contain the
%            requisite set theory axioms. Problems that use this axiom set
%            must supply appropriate set theory axioms.
%--------------------------------------------------------------------------
%----Sigma (union of members).
cnf(union_of_members_1,axiom,
    ( ~ element_of_set(U,union_of_members(Vf))
    | element_of_set(U,f1(Vf,U)) ) ).

cnf(union_of_members_2,axiom,
    ( ~ element_of_set(U,union_of_members(Vf))
    | element_of_collection(f1(Vf,U),Vf) ) ).

cnf(union_of_members_3,axiom,
    ( element_of_set(U,union_of_members(Vf))
    | ~ element_of_set(U,Uu1)
    | ~ element_of_collection(Uu1,Vf) ) ).

%----Pi (intersection of members).
cnf(intersection_of_members_4,axiom,
    ( ~ element_of_set(U,intersection_of_members(Vf))
    | ~ element_of_collection(Va,Vf)
    | element_of_set(U,Va) ) ).

cnf(intersection_of_members_5,axiom,
    ( element_of_set(U,intersection_of_members(Vf))
    | element_of_collection(f2(Vf,U),Vf) ) ).

cnf(intersection_of_members_6,axiom,
    ( element_of_set(U,intersection_of_members(Vf))
    | ~ element_of_set(U,f2(Vf,U)) ) ).

%----Topological space
cnf(topological_space_7,axiom,
    ( ~ topological_space(X,Vt)
    | equal_sets(union_of_members(Vt),X) ) ).

cnf(topological_space_8,axiom,
    ( ~ topological_space(X,Vt)
    | element_of_collection(empty_set,Vt) ) ).

cnf(topological_space_9,axiom,
    ( ~ topological_space(X,Vt)
    | element_of_collection(X,Vt) ) ).

cnf(topological_space_10,axiom,
    ( ~ topological_space(X,Vt)
    | ~ element_of_collection(Y,Vt)
    | ~ element_of_collection(Z,Vt)
    | element_of_collection(intersection_of_sets(Y,Z),Vt) ) ).

cnf(topological_space_11,axiom,
    ( ~ topological_space(X,Vt)
    | ~ subset_collections(Vf,Vt)
    | element_of_collection(union_of_members(Vf),Vt) ) ).

cnf(topological_space_12,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | element_of_collection(f3(X,Vt),Vt)
    | subset_collections(f5(X,Vt),Vt) ) ).

cnf(topological_space_13,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | element_of_collection(f3(X,Vt),Vt)
    | ~ element_of_collection(union_of_members(f5(X,Vt)),Vt) ) ).

cnf(topological_space_14,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | element_of_collection(f4(X,Vt),Vt)
    | subset_collections(f5(X,Vt),Vt) ) ).

cnf(topological_space_15,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | element_of_collection(f4(X,Vt),Vt)
    | ~ element_of_collection(union_of_members(f5(X,Vt)),Vt) ) ).

cnf(topological_space_16,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | ~ element_of_collection(intersection_of_sets(f3(X,Vt),f4(X,Vt)),Vt)
    | subset_collections(f5(X,Vt),Vt) ) ).

cnf(topological_space_17,axiom,
    ( topological_space(X,Vt)
    | ~ equal_sets(union_of_members(Vt),X)
    | ~ element_of_collection(empty_set,Vt)
    | ~ element_of_collection(X,Vt)
    | ~ element_of_collection(intersection_of_sets(f3(X,Vt),f4(X,Vt)),Vt)
    | ~ element_of_collection(union_of_members(f5(X,Vt)),Vt) ) ).

%----Open set
cnf(open_set_18,axiom,
    ( ~ open(U,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(open_set_19,axiom,
    ( ~ open(U,X,Vt)
    | element_of_collection(U,Vt) ) ).

cnf(open_set_20,axiom,
    ( open(U,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ element_of_collection(U,Vt) ) ).

%----Closed set
cnf(closed_set_21,axiom,
    ( ~ closed(U,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(closed_set_22,axiom,
    ( ~ closed(U,X,Vt)
    | open(relative_complement_sets(U,X),X,Vt) ) ).

cnf(closed_set_23,axiom,
    ( closed(U,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ open(relative_complement_sets(U,X),X,Vt) ) ).

%----Finer topology
cnf(finer_topology_24,axiom,
    ( ~ finer(Vt,Vs,X)
    | topological_space(X,Vt) ) ).

cnf(finer_topology_25,axiom,
    ( ~ finer(Vt,Vs,X)
    | topological_space(X,Vs) ) ).

cnf(finer_topology_26,axiom,
    ( ~ finer(Vt,Vs,X)
    | subset_collections(Vs,Vt) ) ).

cnf(finer_topology_27,axiom,
    ( finer(Vt,Vs,X)
    | ~ topological_space(X,Vt)
    | ~ topological_space(X,Vs)
    | ~ subset_collections(Vs,Vt) ) ).

%----Basis for a topology
cnf(basis_for_topology_28,axiom,
    ( ~ basis(X,Vf)
    | equal_sets(union_of_members(Vf),X) ) ).

cnf(basis_for_topology_29,axiom,
    ( ~ basis(X,Vf)
    | ~ element_of_set(Y,X)
    | ~ element_of_collection(Vb1,Vf)
    | ~ element_of_collection(Vb2,Vf)
    | ~ element_of_set(Y,intersection_of_sets(Vb1,Vb2))
    | element_of_set(Y,f6(X,Vf,Y,Vb1,Vb2)) ) ).

cnf(basis_for_topology_30,axiom,
    ( ~ basis(X,Vf)
    | ~ element_of_set(Y,X)
    | ~ element_of_collection(Vb1,Vf)
    | ~ element_of_collection(Vb2,Vf)
    | ~ element_of_set(Y,intersection_of_sets(Vb1,Vb2))
    | element_of_collection(f6(X,Vf,Y,Vb1,Vb2),Vf) ) ).

cnf(basis_for_topology_31,axiom,
    ( ~ basis(X,Vf)
    | ~ element_of_set(Y,X)
    | ~ element_of_collection(Vb1,Vf)
    | ~ element_of_collection(Vb2,Vf)
    | ~ element_of_set(Y,intersection_of_sets(Vb1,Vb2))
    | subset_sets(f6(X,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1,Vb2)) ) ).

cnf(basis_for_topology_32,axiom,
    ( basis(X,Vf)
    | ~ equal_sets(union_of_members(Vf),X)
    | element_of_set(f7(X,Vf),X) ) ).

cnf(basis_for_topology_33,axiom,
    ( basis(X,Vf)
    | ~ equal_sets(union_of_members(Vf),X)
    | element_of_collection(f8(X,Vf),Vf) ) ).

cnf(basis_for_topology_34,axiom,
    ( basis(X,Vf)
    | ~ equal_sets(union_of_members(Vf),X)
    | element_of_collection(f9(X,Vf),Vf) ) ).

cnf(basis_for_topology_35,axiom,
    ( basis(X,Vf)
    | ~ equal_sets(union_of_members(Vf),X)
    | element_of_set(f7(X,Vf),intersection_of_sets(f8(X,Vf),f9(X,Vf))) ) ).

cnf(basis_for_topology_36,axiom,
    ( basis(X,Vf)
    | ~ equal_sets(union_of_members(Vf),X)
    | ~ element_of_set(f7(X,Vf),Uu9)
    | ~ element_of_collection(Uu9,Vf)
    | ~ subset_sets(Uu9,intersection_of_sets(f8(X,Vf),f9(X,Vf))) ) ).

%----Topology generated by a basis
cnf(topology_generated_37,axiom,
    ( ~ element_of_collection(U,top_of_basis(Vf))
    | ~ element_of_set(X,U)
    | element_of_set(X,f10(Vf,U,X)) ) ).

cnf(topology_generated_38,axiom,
    ( ~ element_of_collection(U,top_of_basis(Vf))
    | ~ element_of_set(X,U)
    | element_of_collection(f10(Vf,U,X),Vf) ) ).

cnf(topology_generated_39,axiom,
    ( ~ element_of_collection(U,top_of_basis(Vf))
    | ~ element_of_set(X,U)
    | subset_sets(f10(Vf,U,X),U) ) ).

cnf(topology_generated_40,axiom,
    ( element_of_collection(U,top_of_basis(Vf))
    | element_of_set(f11(Vf,U),U) ) ).

cnf(topology_generated_41,axiom,
    ( element_of_collection(U,top_of_basis(Vf))
    | ~ element_of_set(f11(Vf,U),Uu11)
    | ~ element_of_collection(Uu11,Vf)
    | ~ subset_sets(Uu11,U) ) ).

%----Subspace topology
cnf(subspace_topology_42,axiom,
    ( ~ element_of_collection(U,subspace_topology(X,Vt,Y))
    | topological_space(X,Vt) ) ).

cnf(subspace_topology_43,axiom,
    ( ~ element_of_collection(U,subspace_topology(X,Vt,Y))
    | subset_sets(Y,X) ) ).

cnf(subspace_topology_44,axiom,
    ( ~ element_of_collection(U,subspace_topology(X,Vt,Y))
    | element_of_collection(f12(X,Vt,Y,U),Vt) ) ).

cnf(subspace_topology_45,axiom,
    ( ~ element_of_collection(U,subspace_topology(X,Vt,Y))
    | equal_sets(U,intersection_of_sets(Y,f12(X,Vt,Y,U))) ) ).

cnf(subspace_topology_46,axiom,
    ( element_of_collection(U,subspace_topology(X,Vt,Y))
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | ~ element_of_collection(Uu12,Vt)
    | ~ equal_sets(U,intersection_of_sets(Y,Uu12)) ) ).

%----Interior of a set
cnf(interior_47,axiom,
    ( ~ element_of_set(U,interior(Y,X,Vt))
    | topological_space(X,Vt) ) ).

cnf(interior_48,axiom,
    ( ~ element_of_set(U,interior(Y,X,Vt))
    | subset_sets(Y,X) ) ).

cnf(interior_49,axiom,
    ( ~ element_of_set(U,interior(Y,X,Vt))
    | element_of_set(U,f13(Y,X,Vt,U)) ) ).

cnf(interior_50,axiom,
    ( ~ element_of_set(U,interior(Y,X,Vt))
    | subset_sets(f13(Y,X,Vt,U),Y) ) ).

cnf(interior_51,axiom,
    ( ~ element_of_set(U,interior(Y,X,Vt))
    | open(f13(Y,X,Vt,U),X,Vt) ) ).

cnf(interior_52,axiom,
    ( element_of_set(U,interior(Y,X,Vt))
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | ~ element_of_set(U,Uu13)
    | ~ subset_sets(Uu13,Y)
    | ~ open(Uu13,X,Vt) ) ).

%----Closure of a set
cnf(closure_53,axiom,
    ( ~ element_of_set(U,closure(Y,X,Vt))
    | topological_space(X,Vt) ) ).

cnf(closure_54,axiom,
    ( ~ element_of_set(U,closure(Y,X,Vt))
    | subset_sets(Y,X) ) ).

cnf(closure_55,axiom,
    ( ~ element_of_set(U,closure(Y,X,Vt))
    | ~ subset_sets(Y,V)
    | ~ closed(V,X,Vt)
    | element_of_set(U,V) ) ).

cnf(closure_56,axiom,
    ( element_of_set(U,closure(Y,X,Vt))
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | subset_sets(Y,f14(Y,X,Vt,U)) ) ).

cnf(closure_57,axiom,
    ( element_of_set(U,closure(Y,X,Vt))
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | closed(f14(Y,X,Vt,U),X,Vt) ) ).

cnf(closure_58,axiom,
    ( element_of_set(U,closure(Y,X,Vt))
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | ~ element_of_set(U,f14(Y,X,Vt,U)) ) ).

%----Neighborhood
cnf(neighborhood_59,axiom,
    ( ~ neighborhood(U,Y,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(neighborhood_60,axiom,
    ( ~ neighborhood(U,Y,X,Vt)
    | open(U,X,Vt) ) ).

cnf(neighborhood_61,axiom,
    ( ~ neighborhood(U,Y,X,Vt)
    | element_of_set(Y,U) ) ).

cnf(neighborhood_62,axiom,
    ( neighborhood(U,Y,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ open(U,X,Vt)
    | ~ element_of_set(Y,U) ) ).

%----Limit point
cnf(limit_point_63,axiom,
    ( ~ limit_point(Z,Y,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(limit_point_64,axiom,
    ( ~ limit_point(Z,Y,X,Vt)
    | subset_sets(Y,X) ) ).

cnf(limit_point_65,axiom,
    ( ~ limit_point(Z,Y,X,Vt)
    | ~ neighborhood(U,Z,X,Vt)
    | element_of_set(f15(Z,Y,X,Vt,U),intersection_of_sets(U,Y)) ) ).

cnf(limit_point_66,axiom,
    ( ~ limit_point(Z,Y,X,Vt)
    | ~ neighborhood(U,Z,X,Vt)
    | ~ eq_p(f15(Z,Y,X,Vt,U),Z) ) ).

cnf(limit_point_67,axiom,
    ( limit_point(Z,Y,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | neighborhood(f16(Z,Y,X,Vt),Z,X,Vt) ) ).

cnf(limit_point_68,axiom,
    ( limit_point(Z,Y,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Y,X)
    | ~ element_of_set(Uu16,intersection_of_sets(f16(Z,Y,X,Vt),Y))
    | eq_p(Uu16,Z) ) ).

%----Boundary of a set
cnf(boundary_69,axiom,
    ( ~ element_of_set(U,boundary(Y,X,Vt))
    | topological_space(X,Vt) ) ).

cnf(boundary_70,axiom,
    ( ~ element_of_set(U,boundary(Y,X,Vt))
    | element_of_set(U,closure(Y,X,Vt)) ) ).

cnf(boundary_71,axiom,
    ( ~ element_of_set(U,boundary(Y,X,Vt))
    | element_of_set(U,closure(relative_complement_sets(Y,X),X,Vt)) ) ).

cnf(boundary_72,axiom,
    ( element_of_set(U,boundary(Y,X,Vt))
    | ~ topological_space(X,Vt)
    | ~ element_of_set(U,closure(Y,X,Vt))
    | ~ element_of_set(U,closure(relative_complement_sets(Y,X),X,Vt)) ) ).

%----Hausdorff space
cnf(hausdorff_73,axiom,
    ( ~ hausdorff(X,Vt)
    | topological_space(X,Vt) ) ).

cnf(hausdorff_74,axiom,
    ( ~ hausdorff(X,Vt)
    | ~ element_of_set(X_1,X)
    | ~ element_of_set(X_2,X)
    | eq_p(X_1,X_2)
    | neighborhood(f17(X,Vt,X_1,X_2),X_1,X,Vt) ) ).

cnf(hausdorff_75,axiom,
    ( ~ hausdorff(X,Vt)
    | ~ element_of_set(X_1,X)
    | ~ element_of_set(X_2,X)
    | eq_p(X_1,X_2)
    | neighborhood(f18(X,Vt,X_1,X_2),X_2,X,Vt) ) ).

cnf(hausdorff_76,axiom,
    ( ~ hausdorff(X,Vt)
    | ~ element_of_set(X_1,X)
    | ~ element_of_set(X_2,X)
    | eq_p(X_1,X_2)
    | disjoint_s(f17(X,Vt,X_1,X_2),f18(X,Vt,X_1,X_2)) ) ).

cnf(hausdorff_77,axiom,
    ( hausdorff(X,Vt)
    | ~ topological_space(X,Vt)
    | element_of_set(f19(X,Vt),X) ) ).

cnf(hausdorff_78,axiom,
    ( hausdorff(X,Vt)
    | ~ topological_space(X,Vt)
    | element_of_set(f20(X,Vt),X) ) ).

cnf(hausdorff_79,axiom,
    ( hausdorff(X,Vt)
    | ~ topological_space(X,Vt)
    | ~ eq_p(f19(X,Vt),f20(X,Vt)) ) ).

cnf(hausdorff_80,axiom,
    ( hausdorff(X,Vt)
    | ~ topological_space(X,Vt)
    | ~ neighborhood(Uu19,f19(X,Vt),X,Vt)
    | ~ neighborhood(Uu20,f20(X,Vt),X,Vt)
    | ~ disjoint_s(Uu19,Uu20) ) ).

%----Separation in a topological space
cnf(separation_81,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(separation_82,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | ~ equal_sets(Va1,empty_set) ) ).

cnf(separation_83,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | ~ equal_sets(Va2,empty_set) ) ).

cnf(separation_84,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | element_of_collection(Va1,Vt) ) ).

cnf(separation_85,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | element_of_collection(Va2,Vt) ) ).

cnf(separation_86,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | equal_sets(union_of_sets(Va1,Va2),X) ) ).

cnf(separation_87,axiom,
    ( ~ separation(Va1,Va2,X,Vt)
    | disjoint_s(Va1,Va2) ) ).

cnf(separation_88,axiom,
    ( separation(Va1,Va2,X,Vt)
    | ~ topological_space(X,Vt)
    | equal_sets(Va1,empty_set)
    | equal_sets(Va2,empty_set)
    | ~ element_of_collection(Va1,Vt)
    | ~ element_of_collection(Va2,Vt)
    | ~ equal_sets(union_of_sets(Va1,Va2),X)
    | ~ disjoint_s(Va1,Va2) ) ).

%----Connected topological space
cnf(connected_space_89,axiom,
    ( ~ connected_space(X,Vt)
    | topological_space(X,Vt) ) ).

cnf(connected_space_90,axiom,
    ( ~ connected_space(X,Vt)
    | ~ separation(Va1,Va2,X,Vt) ) ).

cnf(connected_space_91,axiom,
    ( connected_space(X,Vt)
    | ~ topological_space(X,Vt)
    | separation(f21(X,Vt),f22(X,Vt),X,Vt) ) ).

%----Connected set
cnf(connected_set_92,axiom,
    ( ~ connected_set(Va,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(connected_set_93,axiom,
    ( ~ connected_set(Va,X,Vt)
    | subset_sets(Va,X) ) ).

cnf(connected_set_94,axiom,
    ( ~ connected_set(Va,X,Vt)
    | connected_space(Va,subspace_topology(X,Vt,Va)) ) ).

cnf(connected_set_95,axiom,
    ( connected_set(Va,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Va,X)
    | ~ connected_space(Va,subspace_topology(X,Vt,Va)) ) ).

%----Open covering
cnf(open_covering_96,axiom,
    ( ~ open_covering(Vf,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(open_covering_97,axiom,
    ( ~ open_covering(Vf,X,Vt)
    | subset_collections(Vf,Vt) ) ).

cnf(open_covering_98,axiom,
    ( ~ open_covering(Vf,X,Vt)
    | equal_sets(union_of_members(Vf),X) ) ).

cnf(open_covering_99,axiom,
    ( open_covering(Vf,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ subset_collections(Vf,Vt)
    | ~ equal_sets(union_of_members(Vf),X) ) ).

%----Compact topological space
cnf(compact_space_100,axiom,
    ( ~ compact_space(X,Vt)
    | topological_space(X,Vt) ) ).

cnf(compact_space_101,axiom,
    ( ~ compact_space(X,Vt)
    | ~ open_covering(Vf1,X,Vt)
    | finite(f23(X,Vt,Vf1)) ) ).

cnf(compact_space_102,axiom,
    ( ~ compact_space(X,Vt)
    | ~ open_covering(Vf1,X,Vt)
    | subset_collections(f23(X,Vt,Vf1),Vf1) ) ).

cnf(compact_space_103,axiom,
    ( ~ compact_space(X,Vt)
    | ~ open_covering(Vf1,X,Vt)
    | open_covering(f23(X,Vt,Vf1),X,Vt) ) ).

cnf(compact_space_104,axiom,
    ( compact_space(X,Vt)
    | ~ topological_space(X,Vt)
    | open_covering(f24(X,Vt),X,Vt) ) ).

cnf(compact_space_105,axiom,
    ( compact_space(X,Vt)
    | ~ topological_space(X,Vt)
    | ~ finite(Uu24)
    | ~ subset_collections(Uu24,f24(X,Vt))
    | ~ open_covering(Uu24,X,Vt) ) ).

%----Compact set
cnf(compact_set_106,axiom,
    ( ~ compact_set(Va,X,Vt)
    | topological_space(X,Vt) ) ).

cnf(compact_set_107,axiom,
    ( ~ compact_set(Va,X,Vt)
    | subset_sets(Va,X) ) ).

cnf(compact_set_108,axiom,
    ( ~ compact_set(Va,X,Vt)
    | compact_space(Va,subspace_topology(X,Vt,Va)) ) ).

cnf(compact_set_109,axiom,
    ( compact_set(Va,X,Vt)
    | ~ topological_space(X,Vt)
    | ~ subset_sets(Va,X)
    | ~ compact_space(Va,subspace_topology(X,Vt,Va)) ) ).

%--------------------------------------------------------------------------
```
