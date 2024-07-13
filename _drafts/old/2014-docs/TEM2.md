What you want to do is start at the top of the column then work your way
down

FEG gun

Accelerator

Gun coils (Gun1 Gun2) linear combinations of these become gun shift and
tilt

C1

C2

Minilens

Objective prefield

Objective postfield

Center Condensor aperture
-------------------------

epxand and contract concentrically. DO first. Largets aperture is good
only for low mags. High res should use smallest

More coherence aperture, smaller spaerture

more beam sensitive use smaller aperture = less current

Some get blown apart

Stage Hieght
------------

### astigmatism condesnor

one hand on brightness one hand on astigmatism knobs. go back and forth,
try to get that sucker round.

### Gun Shift

Gun coils rarely need adjusting on JEOL 2100

Open up Monitor \> Status . Mark down numbers so you can get back and
undo.

Maintenance \> Alignement menu

Mag = 100kx

Select Gun

Gun shift controls where the beam hits the C1 lens. You want it to hit
on axis, otherwise a) your beam will suck due to abberrations being much
worse off axis b)

spot 1 select GUN deflector, adjust shift x/y knobs

spot 5 select press bight tilt on right control panel or CLA deflector
in menu

bring to cetner with shift x/y

Question: what are shift knobs attached to in deifferent modes.

In CLA attached to beright shift/ condesor shift

In gun it changes gun shift

SOme standard numbers
---------------------

CL1: 2.19

Cl3:2.75

CM:2.45

OL:3.41

### Gun Tilt

Coma.

Anode wobbler - because FEG (What does this wobble exactly? I think it
wobbles to focus length of the initial gun before C1)

expand contrentically.

Compensator
-----------

Tilt X wobbler

adjust ONLY def stig x

### NOW do condesnor stig

press cond stig. make round on both sides of convergence

### Stage

Find the stage height by finding a feature and trying to remove as much
contrast as possible. Other cues are the fresnel firnges. Being out of
focus gives you phase contrast (strangely enough).

TBD on beam ring method (angus) and image x image y (bilge) method

### HR tips

Leave sample in. Let rest for hours. Come when little tmeperture
variation due to sun and A/C, Elevator vibrations, etc. (Night Time is
best time). All these things improve stability of sample position.

Use smallest possible condesnor aperture

FOcusing High Res
-----------------

Dotted rectange tool

Process \>Live \> reduced FFT

adjust objective stigmater to make ring circular.

Adjusting focus changes donut and size of donut, as rings pass over
diffraction spots, atoms change color from light to dark.

look back and forth between FFT and image

What exactly do astigmators control? sometimes they appear to rotate
ellipse rather than deform

Everything dispaperas at perfect focus, want to be a little clockwise of
it

increase exposure time

x800k seems to be practial limit? no rotation compesnators above?

1.5M is machine limit

Some spots are camera artifacts.

amorphous material is lumpy material

edge of sample is a lot better looking

Bend Contours
-------------

If you're not parrallely illuminating, you'll see interesting wiggly
shapes on the sample. This is due to bragg planes bending slightly
thoughout the sample and due to the slightly different covergence angles
of the beam depednign on position on the sample. You actually see this
in the IMAGE. which is kind of odd.

ZOLZ zero order laue zone condition - normal of plane is perpendicular
to electron beam (basically), beam is running inside plane.

You can see lines sometimes at crystalline defects. A screw dislocation
is a winding around

SA Diff mode
------------

The Sa diff mode sets objective lens to a configuration that images the
back focal plane of the first objective lens

Turn brightness ALL the way clockwise to the beep

The Diff Focus knob controls the focus

Mag controls camera length

PLA butt on and dif/stig knobs controls position of projector lens
adjust

Not sure about aperture

Adjust specimen tilt (Dialogue \> operation Tilt buttons) to symmettrize
ewald sphere . Move sample around to avoid secondary patterns.

SUperlattice is lgihter lattice inside

rings is veyr small crystals . Broad rings is amorphous material. See if
matches up to spacing of single crystal dots

SA mode dangerous. Can burn cameras. Keep screen down until dim and
crntral beam blocked

You'll want to place the little wire in front of the central spot to
avoid burning the camera.

Do everything on the fluorescent screen, then one you're good, go to the
camera. Cameras burn easy on SAD mode. Beams are small and intense

EELS
----

You can burn the ever loving crap out of an EELS camera. Lower intesnity
to somewhat (a little less than a timex wtach glow)

Put in GIF camera

change to EELS mode - MAKE SURE INTESNITY IS LOW

EELS sees light atoms easy, heavy atoms harder

The power law background makes them harder to see.

The main peaks are in Gatan slidy card thing

Higher letters are easier to see (L as opposed to M)

You can tilt to stage to try to get symmettry around the central spot

Look for

Press View to see live. Press aciquire to acquire. we did 50-1000 take
exposures. do not expose each fr so long as to saturate the camera.

Pringles chip

Under align in autfilter window

Click Cetner zero loss peak button

click foucs specturm - quick then full. or only full

Maunally can focus with GIF quantum SE control, adjust tab

May require going into help menu and selecting power user.

click on each with white mouse and move around to change

Objective is to get straight thin line.

You can look at the peak value of the electron count grpah, get as high
as possible (indicates you've got it straight)

if in diffraction mode, kx,ky, if in imaging , x ,y.

focusx - minimize kx depedance (roating pringle around verticla axis)

foucsy - minimize coupling be tween ky and E (tilt)

sx - curviness of pringles chip

sy - twistiness like propeller blade

In Main tab

dispersion changes how much raange of eV you've got per pixel (Bending
per change in energy of prism)

0.1 or 0.05 ev/channel for low loss eels - if number too high, you can
burn hole in camera. (more electrons per pixel)

2048 pixels across

EELS \> EELS Atlas to get graph of element/compound

plasmon peaks

EELS\> compute thickness - couldn't get to work before, but whatever

Computed based on an absorption rate by plasmons

Selected area diffraction mode increase dispersion to smallest
0.5/channel

2.5 mm aperture

If graph goes yellow or red, you are hurting the camera. Lower
screen/reduce intensity. Stop immediately.

You can get more intense (Not converged, but LED bright) if you shift to
off the Zero loss peak. first do shift in dim mode, then lower screen,
then increase intensity, then raise screen. Avoid BURN ING CAMERA.

Can click shift and ctrl plus mouse move to shift and scale axes of
graph

Can see band gap at edge of zero loss peak?

Questions: Trade off between capture time and number of frames?

alpha seems to vastly increase my count rate. What up wit dat? more
concentrated beam. Is alhpa beam semiangle?

### Core-Loss EELs

inner shell electrons kicked out

1s -\> 2 pi \*

1s -\> 2 sigma\*

diamond is sp3

graphite sp2 hybirdized

Anitbonding density of states important for eels. Electrons need place
to get kicked to

Near neighbor distribution

EXAFS does similar thing with xrayss. x ray absportion fine structure

EXELFS - electron version - very small areas so it is awesome

Can tell two different glass structures apart

At end, put back in EFTEM mode

Can find Se

Bi is much much harder

shift at 3:15

put back onto orion camera - dont let other users burn my eels

Get Egerton

### Eeels background subtraction

EELS \> Baxkground model \> power law.

Adjust box

shift box

click

EMSA

Cryocycle issues
----------------

? WHat was I going for here?

Heating Holder
--------------

screw in nut rounded side up

tap to make sure won't fall apart

plug in plug smiley side down

Have to press heater spereatly from powerr - heater button connected to
pump

Flow from top down, but doesn't really matter

Blow out water from holder when finished.

Controller is nonlinear
