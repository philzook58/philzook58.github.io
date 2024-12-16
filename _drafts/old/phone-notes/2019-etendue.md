EtendUe

I think that the concept of etendue is vastly underappreciated. It is perhaps the fundamental principle of optics.
Optics is first taught by describing how rays coming out of point sources are manipulated by thin lens and mirrors.
Thinking in terms of point sources is already incorrect. A point source does not exist and the concept can lead to nonsensical or paradoxical conclusions. Every source should be considered as an area, albeit a very small one.
A related issue is knowing where the boundary of classical optics and wave optics lies. This transition is highly related to the transition between classical and quantum mechanics, which is generally better understood intuitively despite being so much conceptually strange. This is probably due to the availability of good pedagogy.
Really th not using etendue means you are describing optical systems in just the wrong framework.

In Classical mechanics (F= ma and all that) , talking about only position and not velocity means you are missing the point. The relevant "space" of mechanics is known as phase space, the combination of both position and momentum. It has the interesting quality that volume of phase space is conserved, a result known as Liouvilles theorem. This fact lies at the core of the physical meaning of phase space volume, which shows up in statistical mechanics as entropy and
The state of a ray is not only the position it currently is at. It is also the direction it is heading. If you want to talk about a density or intensity of rays, it needs to be a function of both position and direction. When you want to integrate this distribution, you need to integrate it with respect to a volume element that includes both the positional volume dx and the directional volume dp.

Etendue can be defined in a couple analogous ways. One way avoids walking about angles at all. Etendue is the product of the differential areas of the source and target the light is heading from and to projected on the direction the ray is headed. dA. n dA.n / R2 with angular factorAnother definition is to note that dA . n / R2 is the definition of a differential element of solid angle domega. This then has more of the flavor of being definable at a point, rather than

Numerical aperture is define as n sin theta where theta is the angular spread at the focal point. People talk about numerical aperture as.

One example I like to think about is the light spreading out from the sun. It is an expamp,e so simple, it will not be mentioned in an optics course. The sun is a source of finite size. At any particular point, there is light coming from all points of the surface of the sun nearest you. When the point is close to the sun, the ray from one edge of the sun has quite a different direction than the ray from the opposite side of the sun. When you are far from the sun, the direction of the two rays are more closely aligned. This corresponds to the fact that the sun looks small to you when you are far away. It's angular diameter is decreased. The total amount of energy is the same on inner and outer spheres. If the radius of the sun is R, the disk of the sun covers

Energy is conserved. The intensity of light per unit area goes down as R2. However at the same time the sun subtends a smaller spherical angle. Spherical angle is defined as the dA/R2. The area of the sun is constant. Hence the product of the total area of the outgoing sphere and the solid angle us tended by the sun remain constant. The intensity of light in etendue phase space stays constant. The spherical geometry makes it easy to calculate the geometrical intensity as E/A. What is happening is as the light travels outward it is spreading in area while concentrating in angle.

Etendue as expressed so far has units of m2. It can be naturally non dimensionalized by the wavelength of the light involved. When etendue is of the order Of 1 ish, one should expect to get wave effects.

Etendue also should have a factor of the index of refraction. Immediately after an interface, the area is the same on both sides, but by snell's law the angular spread del sin theta changes by a factor Of the index of refraction.

With these two examples, we've covered a majority of what light does in classical optics. It goes through changing index of refractions and it free space propagates.
It also reflects.

Numerical aperture is a topic that is naturally understood in terms of etendue. For telescope and microscope systems, the size of the aperture is relevant because the diffraction pattern resulting from the aperture convolves to blurs out an image. The numerical aperture is defined as n sin theta. Where the angle is the angular size of the cone of light at the focal point.
Diffraction phenomenon. There is a a pervading vague sense that diffraction and wave effects occur when the feature size of the slits or screen or thing are on the order of the wavelength of light. This isn't quite right

Huygens principle states that you can replicate the propagation of a wave by considering the superposition of point sources that are proportional to that value of the wave at all points.
Roughly, a point source makes a field e Iomegar/ r
In the far field limit, we can assume that z is much much larger than x or y.
As a rough sketch of Hu

Just as point sources do not exist, neither do perfectly collimated beams. Any beam has finite diameter. This finite diameter is similar to putting the beam through a large hole, which would cause slight diffraction. The larger the hole, the less the diffraction, but it is always there.

Spatial coherence. In order to make a spatially incoherent source coherent, typically you pass it through a pinhole. The cittert van zernike theorem says how big the pinhole needs to be. The answer? Make the etendue connecting the source and pinhole roughly 1.

Etendue also is very helpful for impossibility theorems and tricky machines. Why can you not take the light coming off a hot source and focus it to heat a target even hotter? Thermodynamics says you can't make energy spontaneously go from a colder object to a hotter one.
Etendue is intimately related to entropy as it is very much the analog of classical phase space in mechanics. The entropy in statistical mechanics is the logarithm of the volume of phase space at a given energy.

Sommerfeld had some interesting example in his book that gave me pause. I should look that up
