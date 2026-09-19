/*

# Complicated geometry problem — rectangle, circle, midpoints

ABCD is a rectangle with AB=6 and BC=8.

M is the midpoint of AB.
N is the midpoint of BC.
E is the foot of the B-angle-bisector on AC.

K is the circle centered at B with radius BA.
P is an arbitrary point on K.

Prove:
1. AB is parallel to CD.
2. BC is perpendicular to AB.
3. AM = MB.
4. BN = NC.
5. MN is parallel to AC.
6. MN/AC = 1/2.
7. AE/EC = AB/BC.
8. AE/EC = 3/4.
9. AC^2 = 100.
10. AE = 30/7.
11. EC = 40/7.
12. BP = 6.
13. BP^2 = 36.

The problem deliberately combines independent rule families:
rectangle facts
midpoint and midsegment facts
angle-bisector ratio
Pythagoras
circle/radius semantics
numeric ratio and segment arithmetic
*/

inp:

Triangle(A,B,C)

Triangle(B,C,D)

Segment(A,B)
Segment(B,C)
Segment(C,D)
Segment(D,A)
Segment(A,C)

IsRectangle(A,B,C,D)=true

AB=6
BC=8

M=Midpoint(AB)
N=Midpoint(BC)

E=AngleBisector(B,AC)

K=Circle(B,BA)

P=PointOn(K)

prove:

1. IsParallel(AB,CD)=true

2. IsPerpendicular(AB,BC)=true

3. Distance(A,M)=Distance(M,B)

4. Distance(B,N)=Distance(N,C)

5. IsParallel(MN,AC)=true

6. MN/AC=1/2

7. AE/EC=AB/BC

8. AE/EC=3/4

9. AC^2=100

10. AE=30/7

11. EC=40/7

12. Distance(B,P)=6

13. Distance(B,P)^2=36

proof[1]:
IsRectangle(A,B,C,D)=true -> IsParallel(AB,CD)=true

proof[2]:
IsRectangle(A,B,C,D)=true -> IsPerpendicular(AB,BC)=true

proof[3]:
IsMedian(M,AB)=true -> AM=MB

proof[4]:
IsMedian(N,BC)=true -> BN=NC

proof[5]:
// M and N are midpoints of two sides of triangle ABC.
IsMedian(M,AB)=true && IsMedian(N,BC)=true -> IsParallel(MN,AC)=true

proof[6]:
// Midsegment theorem.
IsParallel(MN,AC)=true -> MN/AC=1/2

proof[7]:
// E is the foot of the B-angle-bisector on AC.
IsAngleBisector(BE,ABC)=true -> AE/EC=AB/BC

proof[8]:
AB=6 && BC=8 -> AB/BC=3/4 -> AE/EC=3/4

proof[9]:
// ABC is right at B.
IsPerpendicular(AB,BC)=true && AB=6 && BC=8 -> AC^2=100

proof[10]:
// AE+EC=AC together with AE/EC=3/4.
AE/EC=3/4 && AC=10 -> AE=30/7

proof[11]:
AE/EC=3/4 && AC=10 -> EC=40/7

proof[12]:
// P lies on the circle centered at B with radius BA=6.
OnCircle(P,K)=true && AB=6 -> BP=6

proof[13]:
BP=6 -> BP^2=36

