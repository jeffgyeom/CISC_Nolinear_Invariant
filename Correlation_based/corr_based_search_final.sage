#!/usr/bin/env sage
#this code supports python2.x only
from sage.all import *
from sage.crypto.boolean_function import BooleanFunction
from sage.crypto.sbox import SBox
import copy
import sys
sys.path.append('../sboxes_info/')
from sboxes import *

#Analysis Threshold
ANALYSIS_BIT_RANGE = 20

#General Information
ALG_NAME = ""
S_BOX  = []
S_BOX_CARDINALITY = 0
S_BOX_BIT_SIZE = 0
S_BOX_BOOLEANS  = []


def set_sbox():
    for i in range(len(SBOXES)):
        print ("%s" % (SBOXES[i][0]))
    chosen = raw_input("> Which S-Box?(e.g., PRESENT):")
    
    global ALG_NAME
    global S_BOX
    global S_BOX_CARDINALITY
    global S_BOX_BIT_SIZE

    chosen_idx = -1
    for i in range(len(SBOXES)):
        if (SBOXES[i][0] == chosen) or (SBOXES[i][0] == chosen.upper()):
            chosen_idx = i
            ALG_NAME = SBOXES[i][0]
            S_BOX = SBOXES[i][1]
            S_BOX_CARDINALITY = len(SBOXES[i][1])
            S_BOX_BIT_SIZE = S_BOX_CARDINALITY.bit_length() - 1

    if chosen_idx == -1:
        print ("error : the S-Box(%s) does not exist" %chosen.upper())


def compute_LAT(S_Box):
    S_BOX_CARDINALITY = len(S_Box)

    odd_even_hamming_table=range(len(S_Box))
    for masked_re in range(len(S_Box)):
        hamming_weight = 0
        for shift in range(S_BOX_CARDINALITY.bit_length()):
            if (((masked_re >> shift) & 1) == 1):
                hamming_weight = hamming_weight + 1
		
        if (hamming_weight & 1) == 1:
            odd_even_hamming_table[masked_re] = -1
        else:
            odd_even_hamming_table[masked_re] = 1

    LAT=range(len(S_Box))
    for i in range(len(S_Box)):
        LAT[i] = range(len(S_Box))
    for o_mask in range(len(S_Box)):
        m_dot_sbox_boolean_f=range(len(S_Box))
        for input in range(len(S_Box)):
            m_dot_sbox_boolean_f[input] = odd_even_hamming_table[o_mask & S_Box[input]]

        outmask_walsh_coeff = walsh_trasform(m_dot_sbox_boolean_f)
        
		#end Walsh with [a fixed outmask]
        for i_mask in range(len(S_Box)):
            LAT[i_mask][o_mask] = outmask_walsh_coeff[i_mask]
    return LAT
	
def walsh_trasform(distribution):
    f = copy.deepcopy(distribution)
    size = len(distribution)
    step  = 1
    while step < size:
        for i1 in range(0,size,2*step):
            for i0 in range(0,step):
                i=i1+i0
                SUM = f[i] + f[i + step]
                DIF = f[i] - f[i + step]
                f[i] = SUM
                f[i + step] = DIF
        step = 2*step
    walsh_coeff = copy.deepcopy(f)
    return walsh_coeff

def inv_walsh_trasform(walsh_coeff):
    f = copy.deepcopy(walsh_coeff)
    size = len(walsh_coeff)
    step  = 1
    while step < size:
        for i1 in range(0,size,2*step):
            for i0 in range(0,step):
                i=i1+i0
                SUM = f[i] + f[i + step]
                DIF = f[i] - f[i + step]
                f[i] = SUM/2
                f[i + step] = DIF/2
        step = 2*step
    distribution = copy.deepcopy(f)
    return distribution

def boolean_to_minus_power(boolean_table):
    f = copy.deepcopy(boolean_table)
    size = len(boolean_table)
    for i in range(size):
        if boolean_table[i] == 0:
            f[i] = 1
        elif boolean_table[i] == 1:
            f[i] = -1
    return f

def minus_power_to_boolean(minus_power_table):
    f =copy.deepcopy(minus_power_table)
    size = len(minus_power_table)
    for i in range(size):
        if minus_power_table[i] == 1:
            f[i] = 0
        elif minus_power_table[i] == -1:
            f[i] = 1
    return f

def is_nonlinear_invariant(S_Box, nonlinear_table):
    init = nonlinear_table[0] ^ nonlinear_table[S_Box[0]]
    flag = 0
    for x in range(1,len(S_Box)):
        if nonlinear_table[x] ^ nonlinear_table[S_Box[x]] != init:
            flag = 1
    if flag == 1:
        return False
    else:
        return True

#Set S-Box
set_sbox()

M = compute_LAT(S_BOX)
M = matrix(QQ, M)
E = matrix.identity( M.nrows() )

M_plus_size_E = M + S_BOX_CARDINALITY * E
M_minus_size_E = M - S_BOX_CARDINALITY * E

eigenspace_with_plus_size_value = M_plus_size_E.right_kernel()
_plus_1_eigen_dim = eigenspace_with_plus_size_value.dimension()
eigenspace_with_minus_size_value = M_minus_size_E.right_kernel()
_minus_1_eigen_dim = eigenspace_with_minus_size_value.dimension()

print("The dimension of eigenspace with lambda  1 : %d" %_plus_1_eigen_dim)
print("The dimension of eigenspace with lambda -1 : %d" %_minus_1_eigen_dim)

#S-Box(x0, x1, x2, x3 ... )
NUM_NON_INVARIANT = 0
NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0
NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0 

#From here : Optional up to # of nonlinear invariants

if S_BOX_CARDINALITY < ANALYSIS_BIT_RANGE:
    boolean = 0x1<<S_BOX_CARDINALITY

    while boolean < (0x2<<S_BOX_CARDINALITY):

        boolean_table = [int(x) for x in bin(boolean)[3:]]
        minus_pow_boolean = boolean_to_minus_power(boolean_table)
        walsh_coeff = walsh_trasform(minus_pow_boolean)
        walsh_coeff_vec = vector(walsh_coeff)

        #Check if the walsh coefficient vector is the eigenvector of M with S_BOX_CARDINALITY or -S_BOX_CARDINALITY eigenvalues.
        if (walsh_coeff_vec in eigenspace_with_plus_size_value or walsh_coeff_vec in eigenspace_with_minus_size_value):
            NUM_NON_INVARIANT+=1
            #Check if the nonlinear invariant has the linear structures.
            if BooleanFunction(boolean_table).has_linear_structure() == 1:
                NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE += 1
                #Check if the nonlinear invariant is balanced.
                if BooleanFunction(boolean_table).is_balanced() == 1:
                    NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE += 1
        boolean+=1

    print ("# of Nonlinear Invariants : %d" % NUM_NON_INVARIANT)
    print ("# of Nonlinear Invariants with Linear Structure : %d" % NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
    print ("# of Balanced Nonlinear Invariants with Linear Structure : %d" % NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
else:
    print("# of nonlinear invariants is too large to analyze.")  