#include <math.h>
#include <sys/timeb.h>
#include <windows.h>

const int Tbyte_size=12,loop_n=64/Tbyte_size,Tsize=1<<Tbyte_size,Tshort_size=4,Tshort=1<<Tshort_size,Tmask=Tsize-1;
const int L=30000000;

ULONG64 L21[Tsize],L43[Tsize];
unsigned int L21_tail[Tshort],long_flag[Tsize];
unsigned char _n[Tsize],pow3_tail[Tshort];
unsigned short Ln_x[Tsize],Ln_x_tail[Tshort],_flag[Tsize],pow3[Tsize];
unsigned int ternary_code[1000000];
unsigned char coded_t[L];

int cur_t_byte,cur_t_bit;


//=============== Initializing  lookup tables ==================

// Forming the lookup table for decoding the 4-bit tail of a 64-bit codeword
// cws - size of output word in bits
void form_ter_table4(int cws) {
ULONG64 p;
int numb,k,k_prev;
unsigned int x;
    for(unsigned int y=0;y<Tshort;y++){
        x=y;
        p=numb=0;
        L21_tail[y]=Ln_x_tail[y]=0;
        k=1; k_prev=0;
        for(int i=0;i<Tshort_size;i+=2,k=k_prev?k:(k?k*3:1),x>>=2) {
            if((x&0x3)==3) {
                L21_tail[y]|=(p<<(numb*cws));
                numb++;
                p=0;
                k_prev=1;
            } else
                p=p*3+(x&0x3)+1;
        }
        Ln_x_tail[y]=p;
        L21_tail[y]|=(p<<(numb*cws));
        pow3_tail[y]=k;
    }
}

// Forming the lookup table for short texts
// cws - size of output word in bits
void form_ter_table_short() {
ULONG64 p;
int numb,k,k_prev;
unsigned int x,y;
    for(unsigned int y=0;y<Tsize;y++){
        x=y;
        p=numb=0;
        L21[y]=_n[y]=Ln_x[y]=L43[y]=0; _flag[y]=0xffff;
        k=1; k_prev=0;
        for(int i=0;i<Tbyte_size;i+=2,k=k_prev?k:(k?k*3:1),x>>=2) {
            if((x&0x3)==3) {
                L21[y]|=(p<<(numb*16));
                numb++;
                p=0;
                _flag[y]=0;
                k_prev=1;
            } else
                p=p*3+(x&0x3)+1;
        }
        _n[y]=numb;
        Ln_x[y]=p;
        L21[y]|=(p<<(numb*16));
        pow3[y]=k;

    }
    form_ter_table4(16);
}

// Forming the lookup table for long texts
void form_ter_table_long() {
ULONG64 p;
int numb,k,k_prev;
unsigned int x,y;
    for(unsigned int y=0;y<Tsize;y++){
        x=y;
        p=numb=0;
        L21[y]=_n[y]=Ln_x[y]=L43[y]=0; _flag[y]=0xffff; long_flag[y]=0xffffff;
        k=1; k_prev=0;
        for(int i=0;i<Tbyte_size;i+=2,k=k_prev?k:(k?k*3:1),x>>=2) {
            if((x&0x3)==3) {
                if(numb<=1)
                    L21[y]|=(p<<(numb*32));
                else
                    L43[y]|=(p<<((numb-2)*32));
                numb++;
                p=0;
                _flag[y]=long_flag[y]=0;
                k_prev=1;
            } else
                p=p*3+(x&0x3)+1;
        }
        _n[y]=numb;
        Ln_x[y]=p;
        pow3[y]=k;
    }
    form_ter_table4(32);
}

// Creating the BCT codeword set
// cur - number of current codeword in the set of codewords of given length
// cur3 - number of codewords of given length
// limit - upper limit for number of codewords
void recursive_ternary(int cur,int cur3, int limit) {
    if(cur<limit) {
        for(int i=0;i<3;i++)
            for(int j=0;j<cur3;j++)
                ternary_code[cur+cur3*i+j]=(ternary_code[cur-cur3+j]<<2)|i;
        recursive_ternary(cur+cur3*3,cur3*3,limit);
    }
}


//=============== Encoding functions ===============
// write one trit, from right to left in each byte
void bit_step() {
        if(cur_t_bit<6)
            cur_t_bit+=2;
        else {
            cur_t_bit=0;
            cur_t_byte++;
        }
}

// write codeword to bitstream
void flush_to_byte_ternary(unsigned int x) {
int i,j;
    while((x&3)!=3) {
        coded_t[cur_t_byte]|=(x&3)<<cur_t_bit;
        bit_step();
        x>>=2;
    }
    coded_t[cur_t_byte]|=3<<cur_t_bit;
    bit_step();
}

// Encoding sequence of integers in ranks array
int encode_ternary(int max_rank,unsigned int* ranks) {
int i;
    for(i=0;i<L;i+=8)
        *(ULONG64*)(coded_t+i)=0;
    cur_t_byte=cur_t_bit=0;
	for(i=0;i<max_rank;i++) {
		flush_to_byte_ternary(ternary_code[ranks[i]]); // write current codeword to the end of a code bitstream
	}
	return cur_t_byte;
}

//================ Decoding functions =============

// Decoding the texts with a dictionary <=64K, Alg. 4 + Alg. 6
int decode_ternary_short(unsigned char* code, unsigned short* out,int Len) {
ULONG64 y,z;
int temp=0,k=0,l,t=0;
unsigned short x;
unsigned short u;
    for(int i=0;i<Len;i+=8) {        // line 2 of Alg. 4
        y=*((ULONG64*)(code+i));                   // line 3 of Alg. 4
        for(int j=0;j<loop_n;j++,y>>=Tbyte_size) { // line 4 of Alg. 4
            x=y&Tmask;                             // line 5 of Alg. 4
            // Process(t,x)
            z=t*pow3[x]+L21[x];                    // line 1 of Alg. 6
            *(ULONG64*)(out+k)=z;                  // line 2 of Alg. 6
            k+=_n[x];                              // line 3 of Alg. 6
            t=(z>>(_n[x]<<4));                     // line 4 of Alg. 6
        }
        // Process_short(t,y)
        z=t*pow3_tail[y]+L21_tail[y];
        *(unsigned int*)(out+k)=z;
        k+=_n[y];
        t=(z>>(_n[y]<<4));
    }
}

// Decoding the texts with a dictionary >64K, Alg. 4 + Alg. 5
int decode_ternary_long(unsigned char* code, unsigned int* out,int Len) {
ULONG64 y;
int temp=0,k=0,l,t=0;
unsigned int x,z;
    for(int i=0;i<Len;i+=8) {       // line 2 of Alg. 4
        y=*((ULONG64*)(code+i));                   // line 3 of Alg. 4
        for(int j=0;j<loop_n;j++,y>>=Tbyte_size) { // line 4 of Alg. 4
            x=y&Tmask;                             // line 5 of Alg. 4
            // Process(t,x)
            z=t*pow3[x];       // line 1 of Alg. 5
            *(ULONG64*)(out+k)=L21[x]+z; // line 2 of Alg. 5
            if(_n[x]>2)                  // line 3 of Alg. 5
                *(ULONG64*)(out+k+2)=L43[x];  // line 4 of Alg. 5
            k+=_n[x];                         // line 7 of Alg. 5
            t=Ln_x[x]+(z&long_flag[x]);       // line 8 of Alg. 5
        }
        // Process_short(t,y)
        z=t*pow3_tail[y];
        *(unsigned int*)(out+k)=L21_tail[y]+z;
        k+=_n[y];
        t=Ln_x_tail[y]+(z&long_flag[y]);
    }
}

// the main function generating the BCT-code
void generate_ternary(int limit) {
    ternary_code[0]=3;
    recursive_ternary(1,1,limit);  // forming the codeword set
    form_ter_table_long();         // forming the decoding lookup table for long texts
   // form_ter_table_short();           // forming the decoding lookup table for short texts
}
