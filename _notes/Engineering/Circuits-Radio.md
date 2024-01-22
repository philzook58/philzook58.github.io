---
layout: post
title: Circuits & Radio
---
- [Circuits](#circuits)
  - [Analog](#analog)
    - [Voltage Divider](#voltage-divider)
    - [Current divider](#current-divider)
    - [Bridges](#bridges)
  - [Low pass](#low-pass)
  - [High Pass](#high-pass)
  - [Op Amps](#op-amps)
  - [Transistors](#transistors)
  - [Transformers](#transformers)
  - [555 Timer chips](#555-timer-chips)
  - [Analyses](#analyses)
  - [Oscillators](#oscillators)
  - [Filter Networks](#filter-networks)
  - [Transmission Lines](#transmission-lines)
- [Radio](#radio)
- [SDR](#sdr)
- [Debugging / Measuring](#debugging--measuring)
- [Simulation](#simulation)
- [PCBs](#pcbs)
- [Digital](#digital)
  - [Discrete Chips 7400](#discrete-chips-7400)
  - [Microcontrollers](#microcontrollers)
- [Misc](#misc)

See also:

- Control

What do you actually do:
Look at the spec sheet and copy the example circuit.

# Circuits

It is surprising and confusing how good people get at electronics without persay being very mathemtical about it.
Some of it is pattern recognition

Circuits are not functions. They are relations
The delusion of perfect sources

## Analog

<https://en.wikipedia.org/wiki/Category:Analog_circuits>

### Voltage Divider

<https://en.wikipedia.org/wiki/Voltage_divider>

### Current divider

<https://en.wikipedia.org/wiki/Current_divider>

### Bridges

## Low pass

## High Pass

## Op Amps

The golden rule.

Integrators
Differentiators

## Transistors

BJT
MOSFET

biasing

Golden rules

Current mirror

## Transformers

## 555 Timer chips

## Analyses

Node and mesh

Laplace transform. Because we care about impulse response

Circuit duality

Lanzcos matrices

## Oscillators

## Filter Networks

Matrices connecting ports to each other. Some compose nice

Polynomal designs

Iterated filters and brillouin book.

## Transmission Lines

Line imppeance

# Radio

Models of antenna

Circuits aren't the circuits you think they are. Shit gets messy

Waveguides

Modulation
Multipliers

Complex signals
smith charts

# SDR

RTL-SDR
<https://en.wikipedia.org/wiki/In-phase_and_quadrature_components> IQ quadrature
lime
gnuradio
hackrf one

# Debugging / Measuring

Multimeter
Oscilloscope [scope tutorial](https://www.youtube.com/playlist?list=PL746BF38BC2E068E0)

# Simulation

Qucs

<https://lushprojects.com/circuitjs/>
<https://www.falstad.com/circuit/>

# PCBs

KiCAD
DIY

# Digital

## Discrete Chips 7400

<https://en.wikipedia.org/wiki/List_of_7400-series_integrated_circuits>
A little bit this kind of thing is just for fun. You can get insanely powerful micorcontrollers for cheap.
You could argue maybe for simplicity or speed or parallelism.
Serial latch

## Microcontrollers

# Misc

Art of electronics - didn't really like this one.
ARRL handbook is really good actually
<https://www.youtube.com/@w2aew>
