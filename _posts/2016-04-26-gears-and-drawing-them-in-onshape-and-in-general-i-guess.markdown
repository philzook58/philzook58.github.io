---
author: philzook58
comments: true
date: 2016-04-26 14:18:43+00:00
layout: post
link: https://www.philipzucker.com/gears-and-drawing-them-in-onshape-and-in-general-i-guess/
slug: gears-and-drawing-them-in-onshape-and-in-general-i-guess
title: Gears and Drawing them in Onshape (and in general I guess)
wordpress_id: 430
---

UPDATE: NVM. https://www.onshape.com/featurescript Use the gear generator feature. It's in the plus sign at the right hand side of the menu bar.

You can make stacked gears using the union function to make the pieces of a differential gear train

------------------------------

Wanted to make some gears. Could use openscad but not super comfortable with it and I kind of don't like how the gear library draws the gears.

https://www.youtube.com/watch?v=TgihDwr7Mmw

This seemed pretty good. However, using circular arcs for the gear teeth is not correct. They are involute curves, curves traced out by

Some good resource books are Shigley's Mechanical Engineering Design, Machinery Handbook and these sites

[https://www.cs.cmu.edu/~rapidproto/mechanisms/chpt7.html](https://www.cs.cmu.edu/~rapidproto/mechanisms/chpt7.html)

[http://www.gearseds.com/files/Approx_method_draw_involute_tooth_rev2.pdf](http://www.gearseds.com/files/Approx_method_draw_involute_tooth_rev2.pdf)

A list of some terminology:

The pitch point is the point of contact between two gears that lies between their centers.

The pitch diameter is how far that point will be from the center of the gear. This tells you how far apart to mount the two gears

The diametral pitch is the number of teeth divided by the pitch diameter. What horrible terminology. It must have units of inverse inches typically. P * D  = N

The circular pitch p is the distance between the same point on each tooth . $ p P = \pi$

At the height of the pitch circle there is just as much tooth as tooth gap.

pressure angle is the angle between tooth profile and diameter at the pitch point.

If two gears have the same diametral pitch and  pressure angle (and appropriate tooth profiles) they'll mesh.

For a rack, the teeth are straight lines with the pressure angle with respect to the normal.

For full cut teeth

the outer diameter is Pitch Diameter + 2/P =

the root diameter is Pitch Diameter - 2/P =

For a rack, it's much easier to work with p

Top of tooth is 1/P = p / $ \pi$

the root diameter is Pitch Diameter - 1/P =

Onshape instructions:

So make sketch. Draw the root circle, pitch circle, and outer diameter circle.

Now we need to find the base circle, the circle from which the involute is unrolled. Make a radial line. Make a perpendicular to that line touching the pitch circle. Make another radial line at the pressure angle from the first. Make a line at the pressure angle from the pitch perpendicular  you drew. These two lines should intersect at 90 degrees. That point lies on the base circle. Make a circle that touches that point.

Now the involute. I decided to go with a spline. Write down the radius of the base circle. Make a radial and a perpendicular to that radial and tangent to the base circle.

Make the same thing a couple of times at intervals of 10 degrees or something. Now, set the length of each of the perpendiculars to the arc length away from the first point, i.e. 10*pi/90 * B, 20*pi/90 * B, 30*pi/90 * B, ... where B is the diameter of the Base circle. Now draw a spline connecting the ends of all these lines. This is a good involute. You can stop when the involute crosses the outer diameter.

Draw a radial to the point where the involute touches the pitch circle. Draw another radial at 360/N/4 degrees away from that point where N is number of teethon the concave side of the involute. Now reflect the involute over this line. You have the other side of this tooth



Draw radials to connect to the root circle and a cap line or arc at the outer diameter.

Now extrude. Use some reasonable fillets on the ends and roots of the teeth. Use circular pattern to make the rest of the teeth.

For a rack, draw three horizontal lines at with spacing 1/P. Draw up from the root line a line at the pressure angle from the vertical. Mark where it crosses pitch line. Make a vertical line p/4 (circular pitch) away from it and reflect the line over it. Close off the top. This is a tooth.

Extrude, fillet, and make a linear pattern.

There ya go.


