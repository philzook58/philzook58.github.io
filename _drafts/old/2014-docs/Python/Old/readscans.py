import scipy as sp
import numpy as np
import matplotlib.pyplot as plt

for j in range(1,15):#15
    if j<10:
       num = str(j).zfill(2)
    else:
        num = str(j).zfill(0)
    f = open('C:\Users\Philip\Downloads\scanzyo\Scan'+num+'.MDI','r')    
    print f.readline()
    parameters =  str.split(f.readline())
    print parameters
    mini = float(parameters[0])
    wavelength = float(parameters[4])
    maxi = float(parameters[5])
    points = int(parameters[6])
    data = []

    data.extend(str.split(f.readline()))
    #while data[len(data)-1] != '':
    for line in f:
        data.extend(str.split(line))
    #print data
    for i in range(len(data)):
        data[i]=int(data[i])

    angles = np.linspace(mini,maxi,points)
    plt.clf()
    plt.plot(angles,data)
    plt.xlabel('2 Theta')
    plt.ylabel('Intensity')
    #plt.show()
    #print data
    name = 'XRay\Scan'+str('%02d' % j)+'.png' 
    plt.savefig(name)

    plt.clf()
    dspacing=wavelength/2/np.sin(sp.pi/180*angles/2)
    plt.plot(dspacing,data)
    plt.xlabel('d (Angstroms)')
    plt.ylabel('Intensity')
    if j >10:
        
        plt.show()
    #print data
    else:
        name = 'XRay\DSpacingScan'+str('%02d' % j)+'.png' 
        plt.savefig(name)
    
    f.close()
    
