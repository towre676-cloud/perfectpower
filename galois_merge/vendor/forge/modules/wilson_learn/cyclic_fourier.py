from __future__ import annotations
import numpy as np

def cyclic_route_coefficient(n:int)->np.ndarray:
    """phi_n(a)=(1-zeta_n^a)/2; at n=2 this is exactly [0,1]."""
    a=np.arange(n)
    return (1-np.exp(2j*np.pi*a/n))/2

def inverse_fourier(x:np.ndarray,axis:int=-1)->np.ndarray:
    return np.fft.ifft(x,axis=axis,norm='ortho')

def forward_fourier(x:np.ndarray,axis:int=-1)->np.ndarray:
    return np.fft.fft(x,axis=axis,norm='ortho')

def frequency_convolution(x:np.ndarray,y:np.ndarray)->np.ndarray:
    """Cyclic convolution in frequency coordinates, normalized consistently with unitary FFT."""
    n=x.shape[-1]
    out=np.zeros_like(np.broadcast_arrays(x,y)[0],dtype=np.result_type(x,y,complex))
    xb,yb=np.broadcast_arrays(x,y)
    for i in range(n):
        for j in range(n): out[..., (i+j)%n]+=xb[...,i]*yb[...,j]/np.sqrt(n)
    return out

def pointwise_product_via_fourier(x:np.ndarray,y:np.ndarray)->np.ndarray:
    return forward_fourier(inverse_fourier(x)*inverse_fourier(y))

def cyclic_fusion_table(n:int,q:int=2):
    if q!=2: raise NotImplementedError
    return [[(a+b)%n for b in range(n)] for a in range(n)]
