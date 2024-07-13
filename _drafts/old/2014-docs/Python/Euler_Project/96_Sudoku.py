
import numpy as np

def loadpuzzle(i):
    f = open('sudoku.txt','r')
    line = f.readline()
    temp = [0]*9
    print line
    """
    while(line != "Grid "+str(i).zfill(2) ): #or line != ''
        
        line = f.readline()
        print line
    """
    #temppuzzle = None
    for row in range(9):
        line = f.readline()
        print line
        
        for col in range(9):
            puzzle[row][col] = int(line[col])
        #puzzle.append(temp)
      
    #return temppuzzle

def row(i):
    return puzzle[:][i]
def column(j):
    return puzzle[j][:]

puzzle = np.zeros((9,9))#[[0]*9]*9
#puzzle =
loadpuzzle(1)
print puzzle
print row(1)
print column(0)
