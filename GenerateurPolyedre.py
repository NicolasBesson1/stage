from z3 import *
from random import randint


'''
#Test de z3
S2=Solver()
x,y=Int("x"),Int("y")

S2.add(x+5==y)
S2.add(y<=23)
S2.add(x>17)
print(S2.check())
'''
satisfaisable=False

# Tant que l'ensemble n'est pas satisfaisable
# donc tant que le polyedre soit vide
while(not(satisfaisable)):
    #Declaration de variables
    S=Solver()
    #A est une matrice de n*m, X est un vecteur de dimension n et B de m
    #n est le nombre d'inconnues du systeme d'innequations
    n=randint(10,12)
    #m est le nombre d'inegalites du systeme
    m=randint(10,12)
    #A[i] correspond aux coefficients des variables a l'inegalite i
    A=[[randint(-10,10) for i in range(n)] for j in range(m)]
    #X est l'ensemble des variables
    X=[Int("x"+str(i)) for i in range(n)]
    #B correspond aux membres de droite de chaque inegalite
    B=[randint(-10,10) for i in range(m)]

    print(A)
    print(B)

    for i in range(len(A)):
        #Termes contient le membre de gauche de l'inegalite:
        
        termes=[]
        for j in range(len(X)):
            termes+=[A[i][j]*X[j]]

        #On ajoute a S l'inegalite:
        # sum(A[i][j]*X[j]) <= B[i]
        S.add(sum(termes)<=B[i])
    print(S.check()==sat)
    satisfaisable=S.check()==sat
    
    
print(S.check())

