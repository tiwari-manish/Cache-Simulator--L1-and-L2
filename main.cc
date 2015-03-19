# include <stdio.h>
using namespace std;
# include <iostream>
# include <sstream>
# include <stdlib.h>
# include <assert.h>
# include <fstream>
# include <string.h>
# include <cmath>
# include <vector>
# include <bitset>

typedef unsigned long long uulong;
typedef unsigned char uchar;
typedef unsigned int uint;


int blockSize;
int sizeL1;
int assocL1;
int sizeL2;
int assocL2;


unsigned int numBlock;
unsigned int memtraffic=0;
unsigned int numSets;
unsigned int numIndex;
unsigned int numOffset;
unsigned int tagOffset[2];
unsigned int indexAddr[2];
unsigned int offset = 0;
unsigned long long addr;
int validL1=0;
int validL2=0;
int evictL1=0;
int evictL2=0;
unsigned int cacheLevel;
unsigned int numHits=0;
unsigned int writeMiss=0,writeMissL2=0;
unsigned int readMiss=0,readMissL2=0;
unsigned int numRead=0,readsL2=0;
unsigned int numWrite=0,writesL2=0;
unsigned int numEvictions=0;
uulong currentCycle = 0,currentCycleL2=0,FIFOcounter=0;;
int policyReplace;
int policyInclusive;
//int cacheL1[][];
//int cacheL2[][];
unsigned int writeback=0;
unsigned int writebackL2=0;
int dirtyL2=0;
int evictL1ex=0;
int evictL2in=0,count=0;
int temp=0;
int countincl=0;

int findBlockL1(int, uulong);
int findBlockL2(int, uulong);
int mov2cache(uulong, int);
int insertBlock(int, uulong);
int checkMinLRUL1(uulong,int);
int checkMinLRUL2(uulong,int);
int lruUpdate(uulong,int,int);
void writeBack(uulong);
uulong calculateTag(uulong, int);
uulong calculateIndex(uulong, int);
uulong calculateoffset(uulong);
int block2Replace(uulong,int);
void write2NextLevel(uulong);
uulong generateAddr(uulong,uulong, int);
uulong hit=0;
uulong indexEx=0;
uulong indext=0;

typedef struct {
   uulong LRUbits;
    uulong tag;
    int address;
    int valid;
    int dirty;
    uulong FIFObits;

} cacheLine;

cacheLine** cacheL1;
cacheLine** cacheL2;



// Function to check memory address in cacheL1

void CacheL1(uulong addr, uchar op, int policyReplace, int policyInclusive) {
    int polReplace = policyReplace;
    int polInclusive = policyInclusive;
    int filledPos,filledPosL2;
    int hitPos;
    if (policyReplace!=1)
       currentCycle++;                 // to count the last access;very useful for LRU counting
    if (op == 'w')
        numWrite++;                    // if write operation then increase write counter
    else
        numRead++;                     // if read operation then increase read counter
    cacheLevel = 0;
    temp=0;                                  // First search in L1 cacheL1
    int findblkL1 = findBlockL1(0, addr);
    uulong index=calculateIndex(addr,0);
    uulong tag=calculateTag(addr,0);
 

    //***************L1 Miss Handling ***********************************************
    if (findblkL1 == -1)
    {   int  hitEx=0;
        if (policyReplace==1)
           currentCycle++;
        currentCycleL2++;
    if (sizeL2!=0)
        readsL2++;
        if (op == 'w')
            writeMiss++;
        else
            readMiss++;
        int filledPosL2;
        filledPos=mov2cache(addr,0);
        lruUpdate(addr,filledPos,0);
        if (evictL1==1 || evictL1ex==1 && sizeL2!=0)
         {
          if(sizeL2!=0)
          {
             writesL2++;
             uulong addrEvict=generateAddr(cacheL1[index][filledPos].tag,index,0);
             uulong indexL3=calculateIndex(addrEvict,1);
             uulong tagL3=calculateTag(addrEvict,1);
             int findblkL3 = findBlockL2(1, addrEvict);
             if (findblkL3!=-1)
             {
                 lruUpdate(addrEvict,findblkL3,1);
                 cacheL2[indexL3][findblkL3].dirty=1;
                 if (cacheL1[index][filledPos].dirty==0 && policyInclusive==2)
                     cacheL2[indexL3][findblkL3].dirty=0;
                 cacheL2[indexL3][findblkL3].valid=1;
             }
             else
             {
                 writeMissL2++;
                 int filledPosL3=mov2cache(addrEvict,1);

                 if(policyInclusive==1 && evictL2in==1)
                    {  // 
                        uulong addrEvictL2=generateAddr(cacheL2[indexL3][filledPosL3].tag,indexL3,1);
                        uulong indexL1=calculateIndex(addrEvictL2,0);
                        uulong tagL1=calculateTag(addrEvictL2,0);
                         int findblkL1e = findBlockL1(0, addrEvictL2);
                         if (findblkL1e != -1)
                         {   
                             if (cacheL1[indexL1][findblkL1e].dirty==1)
                             writebackL2--;
                            cacheL1[indexL1][findblkL1e].dirty=0;
                            cacheL1[indexL1][findblkL1e].valid=0;
                            cacheL1[indexL1][findblkL1e].tag=0;
                         }
                     }
                 lruUpdate(addrEvict,filledPosL3,1);
                 cacheL2[indexL3][filledPosL3].dirty=1;
                 cacheL2[indexL3][filledPosL3].tag=tagL3;
                 cacheL2[indexL3][filledPosL3].valid=1;
                 if (cacheL1[index][filledPos].dirty==0 && policyInclusive==2)
                      cacheL2[indexL3][filledPosL3].dirty=0;
             }
             currentCycleL2++;
         }
         }
        if(sizeL2!=0)   //L2 exists
        {
            int findblkL2 = findBlockL2(1, addr);
            dirtyL2=0;

            //**************cache hit in L2***********************//

            if (findblkL2 != -1 )
                {   filledPosL2=findblkL2;
                     hitEx=1;
                    uulong indexL2=calculateIndex(addr,1);
                    indexEx=indexL2;
                    if (cacheL2[indexL2][findblkL2].dirty==1 && policyInclusive==2)
                           dirtyL2=1;
                }
            // **************Cache Miss in L2**********************//
                else
                {
                    readMissL2++;
                    if(policyInclusive!=2)
                    {
                    uulong indexL2=calculateIndex(addr,1);
                    uulong tagL2=calculateTag(addr,1);
                    filledPosL2=mov2cache(addr,1);
                    if(policyInclusive==1 && evictL2in==1)
                    {   temp=1;
                    indext=indexL2;
                    uulong temp= cacheL2[indexL2][filledPosL2].tag;
                    uulong addrEvictL2=generateAddr(temp,indexL2,1);
                    uulong indexL1=calculateIndex(addrEvictL2,0);
                    uulong tagL1=calculateTag(addrEvictL2,0);                   
                    uulong mytag=calculateTag((((temp<<indexAddr[1])|indexL2)<<offset),0);
                    int findblkL1e = findBlockL1(0, addrEvictL2);
                    if (findblkL1e != -1)
                         {  
                             if (cacheL1[indexL1][findblkL1e].dirty==1)
                             {
                                writebackL2--;
                                countincl++;
                             }
                            cacheL1[indexL1][findblkL1e].dirty=0;
                            cacheL1[indexL1][findblkL1e].valid=0;
                            cacheL1[indexL1][findblkL1e].tag=0;
                            
                         }

                     }


                        cacheL2[indexL2][filledPosL2].tag=tagL2;
                        cacheL2[indexL2][filledPosL2].valid=1;
                        cacheL2[indexL2][filledPosL2].dirty=0;
                    }
                }
        }
         //**********Update LRU for L2 hit or miss****************//

         if(sizeL2!=0  && policyInclusive!=2)
            lruUpdate(addr,filledPosL2,1);
         if(sizeL2!=0  && policyInclusive==2 && hitEx==1)
         {
             lruUpdate(addr,filledPosL2,1);
             cacheL2[indexEx][filledPosL2].valid=0;
         }

         //************Update LRU for L1 miss*********************//

             if (op=='r')
                 cacheL1[index][filledPos].dirty=0;
             if (op == 'w' ||  dirtyL2==1)
         cacheL1[index][filledPos].dirty=1;
         cacheL1[index][filledPos].tag=tag;
         cacheL1[index][filledPos].valid=1;

    }
    else  //means its a hit
    {
        hit++;
        if (policyReplace!=1)
           lruUpdate(addr,findblkL1,0);
        if (op == 'w')
            cacheL1[index][findblkL1].dirty=1;
    }
}
int mov2cache(uulong addr,int cachelevel)
{   evictL1=0;
    evictL2=0;
    evictL1ex=0;
    evictL2in=0;
    uulong tag2;
    tag2= calculateTag(addr,cachelevel);
    int index2= calculateIndex(addr,cachelevel);
    int pos= block2Replace(addr,cachelevel);

    switch (cachelevel)
    {
        case 0:
        {
            if (cacheL1[index2][pos].valid==1 && policyInclusive==2)
            { evictL1ex=1;

            }
            if (cacheL1[index2][pos].dirty==1 && cacheL1[index2][pos].valid==1)
                {
                    writeback++;
                    evictL1=1;
                }
            break;
        }

        case 1:
        {   if (cacheL2[index2][pos].valid==1 && policyInclusive==1)
        {
                evictL2in=1;
                count++;
        }
            if (cacheL2[index2][pos].dirty==1 && cacheL2[index2][pos].valid==1)
                {
                    writebackL2++;
                    evictL2=1;
                }
            break;
        }
    }
    return pos;



}

int lruUpdate(uulong addr,int findblkL1,int cachelevel)
{
    uulong index=calculateIndex(addr,cachelevel);
    if(policyReplace==1)
    {
              if (cachelevel==0)
                 cacheL1[index][findblkL1].FIFObits=currentCycle;
              if (cachelevel==1)
                 cacheL2[index][findblkL1].FIFObits=currentCycleL2;

    }
    else
    {
            if (cachelevel==0)
                 cacheL1[index][findblkL1].LRUbits=currentCycle;
            if (cachelevel==1)
                 cacheL2[index][findblkL1].LRUbits=currentCycleL2;
    }

}

int findBlockL1(int cacheLevel, uulong addr) {
    uulong index, i, tag, pos;
    int assoc;

    pos = assocL1;
    assoc = assocL1;
    tag = calculateTag(addr, cacheLevel);
    index = calculateIndex(addr, cacheLevel);

    for (i = 0; i < assoc; i++) {

        if (cacheL1[index][i].valid==1){
            if (cacheL1[index][i].tag == tag) {
                pos = i;
                break;
            }
        }
    }
    if (pos == assoc){
        return (-1);}
    else
        return (pos);

}

int findBlockL2(int cachelevel, uulong addr) {
    uulong index, i, tag, pos;
    int assoc;

    pos = assocL2;
    assoc = assocL2;

    tag = calculateTag(addr, 1);
    index = calculateIndex(addr, 1);


    for (i = 0; i < assoc; i++) {

        if (cacheL2[index][i].valid==1)
            if (cacheL2[index][i].tag == tag) {
                pos = i;
                break;
            }
    }
    if (pos == assoc)
        return (-1);
    else
        return (pos);

}

int isEmpty(int cacheLevel, uulong addr) {

    return 0;
}

int insertBlock(int cacheLevel, uulong addr) {
    return 0;
}

int checkMinLRUL1(uulong addr, int cachelevel) {
    validL1=0;
    uulong index, i,block2rep,counter;
    int flagValid=0;
    int assoc=assocL1;
    block2rep=assocL1;

    counter=currentCycle;
    //else
      // counter=FIFOcounter;
    index= calculateIndex(addr,cacheLevel);
    for (i = 0; i < assoc; i++)
    {
        if (cacheL1[index][i].valid==0)
        {
            flagValid=1;
            block2rep = i;
            break;
        }
    }
    if (flagValid!=1)
    {   validL1=1;
        for (i = 0; i < assoc; i++)
        {
            switch(policyReplace)
        {
            case 0:
            {
               if (cacheL1[index][i].LRUbits<= counter)
                    {
                        block2rep=i;
                        counter=cacheL1[index][i].LRUbits;
                    }
               break;
            }

            case 1:
            {
                if (cacheL1[index][i].FIFObits<= counter)
                    {
                        block2rep=i;
                        counter=cacheL1[index][i].FIFObits;
                    }
                break;
            }
            case 2:
            {
               if (cacheL1[index][i].LRUbits<= counter)
                    {
                        block2rep=i;
                        counter=cacheL1[index][i].LRUbits;
                    }
               break;
            }
        }

        }
    }
     return block2rep;
}

int checkMinLRUL2(uulong addr, int cachelevel) {
    validL2=0;
    uulong index, i,block2rep,counter;
    int flagValid=0;
    int assoc=assocL2;
    block2rep=assocL2;
    counter=currentCycleL2;

    index= calculateIndex(addr,1);
    for (i = 0; i < assoc; i++)
    {
        if (cacheL2[index][i].valid==0)
        {
            flagValid=1;
            block2rep = i;
            break;
        }
    }
    if (flagValid!=1)
    {   validL2=1;
        for (i = 0; i < assoc; i++)
        {
            if (cacheL2[index][i].LRUbits<= counter)
            {
                block2rep=i;
                counter=cacheL2[index][i].LRUbits;
            }
        }
    }
     return block2rep;
}
void writeBack(uulong addr) {
}

int block2Replace(uulong addr ,int cachelevel)
{
    int pos;
    if (cachelevel==0)
        pos= checkMinLRUL1(addr,0);
    else
        pos= checkMinLRUL2(addr,1);
   //lruUpdate(addr,pos,cachelevel);
   return pos;
}

void write2NextLevel(uulong addr)
{

}
//Function to calculate the TAG associated with the address

uulong calculateTag(uulong addr, int cacheLevel) {
    return ((addr >> (tagOffset[cacheLevel])));
}

//Function to calculate the INDEX associated with the address

uulong calculateIndex(uulong addr, int cacheLevel) {
    uulong tagMask = 0;
    for (int i = 0; i < indexAddr[cacheLevel]; i++) {
        tagMask <<= 1;

        tagMask |= 1;

    }
    uulong temp=(addr >> offset) & tagMask;

    return ((addr >> offset) & tagMask);

}

//Function to calculate the OFFSET associated with the address

uulong calculateoffset(uulong addr) {
    uulong tagMask = 0;
    for (int i = 0; i < offset; i++) {
        tagMask <<= 1;

        tagMask |= 1;

    }
    return ((addr >> (tagMask)));
}

uulong generateAddr(uulong tag,uulong index,int cachelevel)
{

    uulong indext=index;
    int level=cachelevel;
    return((((tag<<indexAddr[level])|indext)<<offset));
}

int main(int argc, char *argv[])
{

    std::ifstream fin;
    FILE * pFile;
    uulong addr;
    uulong setsL2;
    // Cache parameters assignment from use input

    if (argv[1] == 0) {
        printf("input format: ");
        printf("./sim_cache <BLOCKSIZE> <sizeL1> <assocL1> <sizeL2> <assocL2> <REPLACEMENT_POLICY> <INCLUSION_PROPERTY> <trace_file\n");
        exit(0);
    }

     blockSize = atoi(argv[1]);
    sizeL1 = atoi(argv[2]);
    assocL1 = atoi(argv[3]);
    sizeL2 = atoi(argv[4]);
    assocL2 = atoi(argv[5]);
    policyReplace = atoi(argv[6]);
    policyInclusive = atoi(argv[7]);
    char fName[30];
    strcpy(fName,argv[8]);
     // calculate number of sets in each cache: cache size is in KB and block size is in Bytes
    uulong setsL1 = (uulong) (( sizeL1 / blockSize) / assocL1);
    offset = log2(blockSize);
   // cout <<sizeL2<<endl;
    if (sizeL2!=0)
    {
        setsL2 = (uulong) ((sizeL2 / blockSize) / assocL2);
        indexAddr[1] = log2(setsL2);
        tagOffset[1] = indexAddr[1] + offset;
        //cout<<"hi  "<<tagOffset[1]<<endl;

    }
    //calculate index bits
    indexAddr[0] = log2(setsL1);



    // calculate offset bits:same for both caches as block size is same
    

    //calculate number of Tag bits= Address Size-index-offset
    //tagOffset[1] = indexAddr[1] + offset;
    tagOffset[0] = indexAddr[0] + offset;
    
    //calculate Tag Address

    // Declare the cache as per the size and initialize all values to zero to avoid garbage
     cacheL1= new cacheLine*[setsL1];
        for (int i = 0; i < setsL1; ++i)
            cacheL1[i]=new cacheLine[assocL1];

    for (int i = 0; i < setsL1; i++) {
        for (int j = 0; j < assocL1; j++) {
            cacheL1[i][j].tag = 0;
            cacheL1[i][j].valid = 0;
            cacheL1[i][j].LRUbits = j;
            cacheL1[i][j].FIFObits = j;
            cacheL1[i][j].dirty=0;
            
        }



    }

    if (sizeL2!=0)
    {
    cacheL2= new cacheLine*[setsL2];
        for (int i = 0; i < setsL2; ++i)
            cacheL2[i]=new cacheLine[assocL2];
    for (int i = 0; i < setsL2; i++) {
        for (int j = 0; j < assocL2; j++) {
            cacheL2[i][j].tag = 0;
            cacheL2[i][j].valid = 0;
            cacheL2[i][j].LRUbits = j;
            cacheL2[i][j].FIFObits = j;
            cacheL2[i][j].dirty=0;
             
        }

    }
    }

    uchar op;

    char pc_val[20];
    ifstream inFile;
    inFile.open(fName,ios::in);
    while (!inFile.eof())
    {
        inFile>>op>>pc_val;
        if(inFile.eof())
        { break;
        }
        addr=strtoull(pc_val,NULL,16);

            CacheL1(addr, op, policyReplace, policyInclusive);

        }
    inFile.close();
    float missrateL2;
    float missrateL1=float(readMiss+writeMiss)/float(numRead+numWrite);
    if (sizeL2!=0)
        missrateL2=float(readMissL2)/float(readsL2);
    else
        missrateL2=0;
    if (sizeL2==0)
    memtraffic=readMiss+writeMiss+writeback;
    if (sizeL2!=0)
    {
        if (policyInclusive==2)
            memtraffic=readMissL2+writebackL2;
        if (policyInclusive!=2)
            memtraffic=readMissL2+writebackL2+countincl;

    }

    cout<<"============Simulator Configuration============"<<endl;

    cout<<" BLOCKSIZE:           "<<blockSize<<endl;
    cout<<" L1_SIZE:             "<<sizeL1<<endl;
    cout<<" L1_ASSOC:            "<<assocL1<<endl;
    cout<<" L2_SIZE:             "<<sizeL2<<endl;
    cout<<" L2_ASSOC:            "<<assocL2<<endl;
    cout<<" REPLACEMENT POLICY:  "<<policyReplace<<endl<<endl;
    cout<<" INCLUSION POLICY:    "<<policyInclusive<<endl;
    cout<<" trace_file:          "<<fName<<endl;
    cout<<"============Simulation results (raw)============"<<endl;
    cout<<" a. Number of L1 reads:        "<<numRead << endl;
    cout<<" b. Number of L1 read misses:  "<<readMiss << endl;
    cout<<" c. Number of L1 writes:       "<<numWrite << endl;

    cout<<" d. Number of L1 write misses: "<<writeMiss << endl;
    cout<<" e. L1 miss rate:              "<<missrateL1<<endl;
    cout<<" f. number of L1 write backs:  "<<writeback<<endl;
    cout<<" g. Number of L2 reads:        "<<readsL2 << endl;
    cout<<" h. Number of L2 read misses:  "<<readMissL2 << endl;
    cout<<" i. Number of L2 writes:       "<<writesL2 << endl;

    cout<<" j. Number of L2 write misses: "<<writeMissL2 << endl;
    cout<<" k. L2 miss rate:              "<<missrateL2<<endl;
    cout <<" l. number of L2 writebacks:   "<<writebackL2<<endl;
    cout <<" m. total memory traffic:      "<<memtraffic<<endl;
  
}
