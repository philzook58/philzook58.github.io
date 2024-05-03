<https://ctms.engin.umich.edu/CTMS/index.php?example=InvertedPendulum&section=SystemModeling> matlab simulink

<https://www.youtube.com/watch?v=qjhAAQexzLg&ab_channel=SteveBrunton> steve brunton

chracterizing the system.
Pendulum length. Natural frequency

The basic pumping controller adds energy to the pendulum. You want to move the motor in sync with the angular velcoity. The direciton you want to move chanes depending on whether you arer above or below the horizontal.

TB220A1
<https://www.sparkfun.com/products/14451> SparkFun Motor Driver - Dual TB6612FNG

# include "STM32encoder.h"

STM32encoder enc(TIM4);

<https://github.com/gianni-carbone/STM32encoder/tree/dc6cf689438c36cee86296a8c01e3f34aacef692> we needed to download the zip

A3 seems to work for reasing pendulum data

The screen
B5 scl
B4 sda

Adafruit 1306 library seems to be working. SPI control. SCL pin I assume is MOSI

```
// Declaration for SSD1306 display connected using software SPI (default case):
#define OLED_MOSI   PB4
#define OLED_CLK   PB5
#define OLED_DC    PA15
#define OLED_CS    12
#define OLED_RESET PB3
```

So A4 is a user led

We installed stmduino
Spent a couple frustrating hours with some unknowable "linker" error because we used a stale arduino from the ubuntu software store.

We had to upgrade our stlink firmware <https://www.st.com/en/development-tools/stsw-link007.html>
Tried it on the blue pill first.
We pulled the stock binary off using the stlink-gui. We could reflash it.

I installed te stmcubeide. It is incredibly overwhelming

STM32F103C8T8 is what the aliexpress said
Generic STM32F1 seems to work

There was a small chance we had to use an exported binary

<https://libopencm3.org/> might be interesting to explore

CMSIS

<https://github.com/playfultechnology/pid-invertedpendulum>

```
Use veed.io to add Chinese subtitles to video tutorial
Then use Google Translate to translate subtitles to ENglish

IO No. Resource Description Peripheral Remarks
A4 Common IO LED lights Peripheral resources on the microcontroller
A15, B3, B4, B5 Common IO OLED display Peripheral resources on the microcontroller
A9, A10 serial port 1 MicroUSB program download, host computer waveform display
A5 External interrupt line 5 User button Used to turn on or off the motor (peripheral resources on the microcontroller)
A7, A11, A12 External interrupt lines 7, 11, 12 Buttons on the adapter board Used to adjust the size of PID parameters
A2 Buttons on the common IO adapter board Reserved buttons, select the swing mode, change the balance point of the swing
B12, B13 Common IO motor Control motor direction
B1 PWMB Motor Motor PWM control signal
B6, B7 THM4_CH1, CH2 Motor encoder Encoder acquisition
A3, A6 ADC1_IN3, IN6 ADC acquisition Collect angular displacement sensor information, voltage measurement
Idle pins A0, A1, A8, B0, B2, B8, B9, B10, B11, B14, B15, C13, C14, C15 
```

So it sounds like
B12 B13 are direction
B1 PWM motor control.
B6 B7 is motor encoder
A3 A6 ADC potentiometer. A3 is labelled at the potentiometer. I don't know that A6 is anything

Hmm. It seems the 3.3 is supplied by the top board to bias the potentiometer

<https://www.aliexpress.us/item/3256802371448872.html?spm=a2g0o.order_list.order_list_main.5.57f71802zybWe0&gatewayAdapt=glo2usa#nav-review>

<http://www.minibalance.com/>

Arm keil studio
<https://marketplace.visualstudio.com/items?itemName=Arm.keil-studio-pack>

simulnik
modelica

<https://github.com/Keshav2829/InvertedPendulumwithSwingUp-on-STM32>

<https://www.aliexpress.us/item/3256804100478690.html?gatewayAdapt=glo2usa4itemAdapt>

LQR controller
energy controller

<https://community.st.com/t5/stm32-mcus-embedded-software/boot0-boot1-pins-boot-mode-doubt/td-p/472463>
boot0 boot1 pin.

<https://github.com/stlink-org/stlink>

<https://github.com/philzook58/cart_pole> our old repo ?
