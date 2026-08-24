inp:
Triangle(A,B,C,[acute=true])

// Seven matched points on AB and AC.
// Each next point is constructed by a midpoint, so the two chains
// have the same affine ratio from A.

D=Midpoint(AB)
E=Midpoint(AD)
F=Midpoint(DE)
G=Midpoint(EF)
H=Midpoint(FG)
I=Midpoint(GH)
J=Midpoint(HI)

K=Midpoint(AC)
L=Midpoint(AK)
M=Midpoint(KL)
N=Midpoint(LM)
O=Midpoint(MN)
P=Midpoint(NO)
Q=Midpoint(OP)

// Perpendiculars from D..J to BC.
R=Intersection(PerpendicularLine(D,BC),BC)
S=Intersection(PerpendicularLine(E,BC),BC)
T=Intersection(PerpendicularLine(F,BC),BC)
U=Intersection(PerpendicularLine(G,BC),BC)
V=Intersection(PerpendicularLine(H,BC),BC)
W=Intersection(PerpendicularLine(I,BC),BC)
X=Intersection(PerpendicularLine(J,BC),BC)

prove:
1. IsParallel(DK,BC)=true
2. IsParallel(EL,BC)=true
3. IsParallel(FM,BC)=true
4. IsParallel(GN,BC)=true
5. IsParallel(HO,BC)=true
6. IsParallel(IP,BC)=true
7. IsParallel(JQ,BC)=true

8. IsPerpendicular(DR,BC)=true
9. IsPerpendicular(ES,BC)=true
10. IsPerpendicular(FT,BC)=true
11. IsPerpendicular(GU,BC)=true
12. IsPerpendicular(HV,BC)=true
13. IsPerpendicular(IW,BC)=true
14. IsPerpendicular(JX,BC)=true
15. IsPerpendicular(DK,DR)=true
16. IsPerpendicular(DK,ES)=true
17. IsPerpendicular(DK,FT)=true
18. IsPerpendicular(DK,GU)=true
19. IsPerpendicular(DK,HV)=true
20. IsPerpendicular(DK,IW)=true
21. IsPerpendicular(DK,JX)=true
22. IsPerpendicular(EL,DR)=true
23. IsPerpendicular(EL,ES)=true
24. IsPerpendicular(EL,FT)=true
25. IsPerpendicular(EL,GU)=true
26. IsPerpendicular(EL,HV)=true
27. IsPerpendicular(EL,IW)=true
28. IsPerpendicular(EL,JX)=true
29. IsPerpendicular(FM,DR)=true
30. IsPerpendicular(FM,ES)=true
31. IsPerpendicular(FM,FT)=true
32. IsPerpendicular(FM,GU)=true
33. IsPerpendicular(FM,HV)=true
34. IsPerpendicular(FM,IW)=true
35. IsPerpendicular(FM,JX)=true
36. IsPerpendicular(GN,DR)=true
37. IsPerpendicular(GN,ES)=true
38. IsPerpendicular(GN,FT)=true
39. IsPerpendicular(GN,GU)=true
40. IsPerpendicular(GN,HV)=true
41. IsPerpendicular(GN,IW)=true
42. IsPerpendicular(GN,JX)=true
43. IsPerpendicular(HO,DR)=true
44. IsPerpendicular(HO,ES)=true
45. IsPerpendicular(HO,FT)=true
46. IsPerpendicular(HO,GU)=true
47. IsPerpendicular(HO,HV)=true
48. IsPerpendicular(HO,IW)=true
49. IsPerpendicular(HO,JX)=true
50. IsPerpendicular(IP,DR)=true
51. IsPerpendicular(IP,ES)=true
52. IsPerpendicular(IP,FT)=true
53. IsPerpendicular(IP,GU)=true
54. IsPerpendicular(IP,HV)=true
55. IsPerpendicular(IP,IW)=true
56. IsPerpendicular(IP,JX)=true
57. IsPerpendicular(JQ,DR)=true
58. IsPerpendicular(JQ,ES)=true
59. IsPerpendicular(JQ,FT)=true
60. IsPerpendicular(JQ,GU)=true
61. IsPerpendicular(JQ,HV)=true
62. IsPerpendicular(JQ,IW)=true
63. IsPerpendicular(JQ,JX)=true
