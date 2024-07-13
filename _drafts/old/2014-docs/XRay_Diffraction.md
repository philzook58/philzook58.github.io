Introduction {#introduction .unnumbered}
============

X-Ray Diffraction is a powerful technique in material science. Imagine
you are blindfolded and have pillows strapped to your hands. You need to
examine a sculpture of a cat. Getting accurate information about its
shape is impossible if the sculpture is a small figurine, but not so
hard if the cat is Mount Rushmore sized. A somewhat analogous thing
occurs with light. We do not readily notice such effects because visible
light has a wavelength $\sim500nm$, a size much smaller than that
encountered in day to day life. However, molecular and atomic distances
are orders of magnitude smaller than this. Because the X-rays have such
a wavelength $\sim1\ifmmode\begingroup\def\b@ld{bold}
  \text{\ifx\math@version\b@ld\bfseries\fi\AA}\endgroup\else\AA\fi$,
they are capable of probing these molecular distances.

Laue Diffraction Condition {#laue-diffraction-condition .unnumbered}
--------------------------

X-Rays are approximated as an incoming plane wave

$$I(r)=Ae^{ik\cdot r}$$

The wave vector k is defined such that

$$|k|=\frac{2\pi}{\lambda}$$

and the direction is the direction of propagation of the wave.

The atoms will scatter the light, but not change its energy much,
maintaining the magnitude of the wave vector but changing its direction

$$k_{1}\rightarrow k_{2}$$

$$|k_{1}|=|k_{2}|$$

Making the approximating that the light is scattered only once and that
the magnitude is independent of the distance to the screen, the
intensity of the scattered light is given by

$$I(r)=\int dr_{1}\rho(r_{1})e^{ik_{1}\cdot r_{1}+ik_{2}\cdot r_{2}}$$

$\rho(r)$is a measure of the ability of the substance at the location r
to scatter light.

![Geometry of Scattering](diffractiondiagram.png)

We can make some substitutions into this formula

$$r=r_{1}+r_{2}$$

$$I(r)=\int dr_{1}\rho(r_{1})e^{ik_{1}\cdot r_{1}+ik_{2}\cdot(r-r_{1})}$$

$$=e^{ik_{2}\cdot r}\int dr_{1}\rho(r_{1})e^{i(k_{1}-k_{2})\cdot r_{1}}$$

For a crystal $\rho(r)$ will be a periodic function with the translation
symmetry of the lattice. For simplicity, we will use the delta
function,$\delta(r)$.

$$\rho(r)=\sum_{m=0}^{M}\sum_{n=0}^{N}\sum_{l=0}^{L}\delta(r-ma_{1}-na_{2}-la_{3})$$

Where $a_{j}$ are the lattice vectors

$$\begin{aligned}
I(r) & \varpropto & \sum_{m=0}^{M}\sum_{n=0}^{N}\sum_{l=0}^{l}e^{i(k_{1}-k_{2})\cdot(r-ma_{1}-na_{2}-la_{3})}\nonumber \\
 & = & e^{i(k_{1}-k_{2})\cdot r}(\sum_{m=0}^{M}e^{-i(k_{1}-k_{2})\cdot ma_{1}})\cdot\nonumber \\
 &  & (\sum_{n=0}^{N}e^{-i(k_{1}-k_{2})\cdot na_{2}})(\sum_{l=0}^{l}e^{-i(k_{1}-k_{2})\cdot la_{3}})\end{aligned}$$

These sums are in the form of a geometric series, which has a simple
closed form solution

$$\sum_{m=0}^{M}e^{-i(k_{1}-k_{2})\cdot ma_{1}}=\frac{1-e^{-i(k_{1}-k_{2})\cdot Ma_{1}}}{1-e^{-i(k_{1}-k_{2})\cdot a_{1}}}$$

Making the substitution

$$G=k_{1}-k_{2}$$

The measured amplitude is proportional to the absolute value of the
intensity squared

$$A(r)=|I(r)|^{2}=\frac{\sin^{2}(\frac{MG\cdot a_{1}}{2})}{\sin^{2}(\frac{G\cdot a_{1}}{2})}\frac{\sin^{2}(\frac{NG\cdot a_{2}}{2})}{\sin^{2}(\frac{G\cdot a_{2}}{2})}\frac{\sin^{2}(\frac{LG\cdot a_{3}}{2})}{\sin^{2}(\frac{G\cdot a_{3}}{2})}$$

The Large maximum of this function will occur when

$$G\cdot a_{j}=(k_{1}-k_{2})\cdot a_{j}=n_{j}2\pi$$

where $n_{j}$is an integer

![Plot of $\frac{\sin^{2}(5x)}{\sin^{2}(x)}$](sinc_plot.png)

The reciprocal lattice vectors are defined such that they satisfy the
relation

$$a_{i}\cdot b_{j}=2\pi\delta_{ij}$$ We can define 3 such vectors in the
following manner.

$$b_{1}=\frac{2\pi a_{2}\times a_{3}}{a_{1}\cdot(a_{2}\times a_{3})}$$

$$b_{2}=\frac{2\pi a_{3}\times a_{1}}{a_{1}\cdot(a_{2}\times a_{3})}$$

$$b_{3}=\frac{2\pi a_{1}\times a_{2}}{a_{1}\cdot(a_{2}\times a_{3})}$$

We now can use these vectors to state the Laue diffraction condition as

$$G=k_{1}-k_{2}=pb_{1}+qb_{2}+rb_{3}$$ Constructive interference occurs
when the difference in the incoming and outgoing wave vector an an
integer sum of the reciprocal lattice of the crystal.

A set of crystal planes can be represented by their normal vector. It is
the common convention to express this normal vector in terms of the
reciprocal lattice vectors, for which it has a simple form.

$$g_{hkl}=hb_{1}+kb_{2}+lb_{3}$$

The indices h,k,l are known as the miller indices of the crystal plane
when they have been reduced such that they possess no common integer
divisor. The distance between two planes is given by the

$$d_{hkl}=\frac{2\pi}{|g_{hkl}|}$$

The elastic condition assumes that the wave vector of the light does not
change in magnitude when it is reflected off of a lattice site.

$$|k_{1}-k_{2}|=n|g_{hkl}|=n|hb_{1}+kb_{2}+lb_{3}|$$

We can use the law of cosines to evaluate $|k_{1}-k_{2}|$. The angle
between the two vectors is $2\theta$.

$$\begin{aligned}
|k_{1}-k_{2}| & = & \sqrt{k_{1}^{2}+k_{2}^{2}-2k_{1}k_{2}\cos(2\theta)}\nonumber \\
 & = & k\sqrt{2-2\cos(2\theta)}=2k\sin(\theta)\end{aligned}$$

$$2\frac{2\pi}{\lambda}\sin(\theta)=n\frac{2\pi}{d_{hkl}}$$

$$2d_{hkl}\sin(\theta)=n\lambda$$

This is known as the Bragg Condition

Powder and Laue Method of X-Ray Diffraction {#powder-and-laue-method-of-x-ray-diffraction .unnumbered}
-------------------------------------------

The Ewald sphere is a geometrical construction on the reciprocal lattice
that allows visualization of the diffraction condition of a crystal. A
2d slice of the reciprocal lattice is plotted and the initial k vector
is placed starting at a lattice point. The possible scattered wave
vectors k' constructs a sphere from the tip of k. If this sphere touches
another reciprocal lattice point, then the difference $K=k-k'$ is an
integer multiple of reciprocal lattice vectors, i.e. the Laue condition.
The angle between k and k' is $2\theta$

![The Ewald Sphere (Source: Ashcroft & Mermin)](ewald.png)

In the powder method of x-ray diffraction , the crystal sample is
crushed into a powder. In this form, the small crystals should have
random orientation, allowing all Bragg diffraction conditions to be
satisfied.

Since we defined the reciprocal lattice in vector notation, we can be
assured that reciprocal lattice transforms under rotations in the same
way as the crystal lattice does. The random orientation of the crystals
in the powder means that all orientations of the reciprocal lattice are
roughly equally possible, and that odds are that at least one small
crystal will have an orientation to satisfy any of the possible
diffraction conditions of the incoming wave vector. In the Ewald sphere
construction, this can be visualized as allowing every rotation of every
lattice point. If the Ewald sphere touches one of these circles,
diffraction will occur

![The Ewald Sphere of Powder Diffraction (Source: Ashcroft & Mermin)
](ewaldpowder.png)

In the Laue Method, a single crystal sample is used with radiation
consisting of a spread of wavelengths. Although the orientation of the
crystal and the direction of the incoming radiation is fixed, the Bragg
condition for multiple planes can be satisfied. In the Ewald sphere
construction this is visualized as allowing a range of Ewald sphere
radii as seen in Figure [1](#fig:lauesphere){reference-type="ref"
reference="fig:lauesphere"}

![The Ewald Sphere of Laue Diffraction (Source: Ashcroft &
Mermin)[\[fig:lauesphere\]]{#fig:lauesphere
label="fig:lauesphere"}](Laueewald.png "fig:"){#fig:lauesphere}[\[laue\]]{#laue
label="laue"}

Procedure {#procedure .unnumbered}
=========

Powder X-Ray Diffraction was carried out on a Rigaku X-Ray machine with
an automated goniometer in the $\theta-2\theta$ configuration. Using
1.541$\ifmmode\begingroup\def\b@ld{bold}
  \text{\ifx\math@version\b@ld\bfseries\fi\AA}\endgroup\else\AA\fi$
wavelength radiation, the machine was calibrated using a known Silicon
powder sample to avoid a systematic offset. Three unknown powder
samples, samples 2, 3, & 5 were analyzed over the $2\theta$ranges of
$4^{\circ}-128^{\circ}$with a step resolution of $0.02^{\circ}$. For the
Laue back scatter photograph, the same X-Ray source was used with a
Polaroid camera upon a unknown orientation Silicon sample. This data was
analyzed graphically using Greninger and Wulff charts.

Results & Analysis {#results-analysis .unnumbered}
==================

   $2\theta$   $d_{hkl}$   Relative Intensity
  ----------- ----------- --------------------
     40.48       2.226             1
     73.68       1.285            0.19
     58.58       1.574           0.134
    101.38       0.996           0.099
     87.6        1.113           0.067
     115.7       0.910           0.023

  : Unknown Slide 2

![Unknown Slide 2](Python/Xray/11.png)

   $2\theta$   $d_{hkl}$   Relative Intensity
  ----------- ----------- --------------------
     38.22      2.3528             1
     44.44     2.036894           0.33
     64.52       1.443           0.213
     77.46       1.231           0.159
     81.66       1.178           0.117
    110.56       0.937           0.081
    111.02      0.9345           0.066

  : Unknown Slide 3

![Unknown Slide 3 ](Python/Xray/12.png)

   $2\theta$   $d_{hkl}$   Relative Intensity
  ----------- ----------- --------------------
     43.44       2.081             1
     50.6        1.802           0.441
     74.22       1.277           0.194
     90.02       1.089           0.175
     94.3        1.051           0.064

  : Unknown Slide 5

![Unknown Slide 5](Python/Xray/14.png)

![Laue Photograph](C:/Users/Philip/Downloads/Laue2.tif)

The intensity was calculated using the area under full-width of half
height for each peak, normalized by the largest peak. The order of
intensity and $d_{hkl}$values of the peaks were found to be consistent
with Slide 2 being Tungsten, Slide 3 being Silver, and Slide 5 being
Copper. The intensity and $d_{hkl}$ values of Gold are quite similar to
those of Silver, close enough to perhaps not be distinguishable by the
$d_{hkl}$ spacing alone, but the intensity data was much closer to
Silver. Further muddying the waters, the sample appeared silver in color
on the back but golden on the front. Similarly Tungsten and Molybdenum
have very close $d_{hkl}$ spacing, but the intensity data was sufficient
to differentiate them. This was perhaps to be expected, as both these
pairs of elements are on adjacent periods on the periodic table, a
situation that often implies similar atomic and chemical properties.

    Tungsten    $2.24_{x}$   1.29$_{2}$   1.58$_{2}$   0.85$_{2}$   1.00$_{1}$   1.12$_{1}$   0.91$_{1}$   0.79$_{1}$
  ------------ ------------ ------------ ------------ ------------ ------------ ------------ ------------ ------------
   Molybdenum   $2.23_{x}$   $1.29_{4}$   $1.57_{2}$   $0.84_{3}$   $1.00_{2}$   $1.11_{1}$   $0.91_{1}$   $0.00_{1}$
     Silver     2.36$_{x}$   2.04$_{4}$   1.23$_{4}$   1.45$_{3}$   0.94$_{2}$   0.83$_{1}$   1.18$_{1}$   0.91$_{1}$
     Copper     2.09$_{x}$   1.81$_{5}$   1.28$_{2}$   1.09$_{2}$   0.83$_{1}$   0.81$_{1}$   1.04$_{1}$   0.90$_{1}$

  : $d_{hkl}$in Order of Intensity (Source:X-Ray Powder Diffraction
  File)

The Laue photograph was analyzed by taking the Greninger chart and
overlaying it on the photograph, with the cetner of the chart and the
center of the graph aligned. The locations of hyperbolic curves of
diffraction peaks were plotted on the chart. The angles $\gamma$and
$\delta$ were read from the chart and then plotted on the Wulff Net,
which is a stereogrpahic projection of the great circles of a sphere. A
second Wulff Net was overlayed the first and rotated until one of the
great circles lied parallel to the graphed points. The zone axis was
plotted $90^{\circ}$down from this great circle on the center of the
Wulff Net. This procedure was repeated for multiple hyperbola and then
the resulting poles were compared to tabulated pole charts. The pole
chart that closely corresponded to the poins plotted was that of an
(111) plane normal to the incoming X-Rays

![Wulff Stereographic Projection. The center points are plotted
hyperbola from the Laue photograph. The points on the exterior are the
zone axis pole points.](C:/Users/Philip/Downloads/Wolff2.png)

![Pole Figure of the (111) Plane Normal to Incoming
X-Rays.](C:/Users/Philip/Downloads/poleplot111.png)

Conclusion {#conclusion .unnumbered}
==========

Three unknown slides were identified using powder X-ray diffraction
technique. Slide 2 was determined to be Tungsten, Slide 3 was Silver,
and Slide 5 was Copper. The Silicon smaple was dtermined to have the
(111) directio normal to incoming X-Rays by taking a Laue
back-scattering photograph, and then analyzing this photograph with the
techniques of Greninger charts and Wulff Nets.

X-Ray diffraction is an indispensable technique for material science,
allowing the experimental determination of the molecular structure or
identity of crystalline materials in a systematic manner. The technique
is made easily accessible to many thanks to the availability of ordered
tabulated data for many substances and ready made machinery.

1 "X-Ray Diffraction Manual" Brown Physics Lab Manual

N. Ashcroft & N. Mermin "Solid State Physics." Cengage Learning 1976

B.C. Cullity "Elements of X-Ray Diffraction" Addison-Wesley, New York,
1956
