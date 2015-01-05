﻿﻿﻿#ifndef _FACTSYSTEMH_
#define _FACTSYSTEMH_
#ifdef INFORMATION
Copyright (C) 2011-2014 by Bruce Wilcox

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#endif

#define MAX_FACT_NODES 800000 

typedef struct FACT 
{  
	unsigned int flags;		

 	FACTOID subjectHead;	
	FACTOID verbHead;		
	FACTOID objectHead;		

    FACTOID subjectNext;	
 	FACTOID verbNext;		
    FACTOID objectNext;  	

	MEANING subject;		
	MEANING verb;			
    MEANING object;	
} FACT;

extern FACT* factBase;		//   start of fact space
extern FACT* factEnd;		//   end of fact space
extern FACT* currentFact;	//   most recent fact found or created
extern FACT* wordnetFacts;	//   end of wordnet facts (before topic facts)
extern FACT* build0Facts;	//   end of build0 facts (start of build1 facts)
extern FACT* factFree;		//   end of facts - most recent fact allocated (ready for next allocation)

// pre-reserved verb types
extern MEANING Mmember;
extern MEANING Mexclude;
extern MEANING Mis;

extern size_t maxFacts;		// allocation limit of facts

void SortFacts(char* set);

// fact index accessing
FACTOID Fact2Index(FACT* F);
FACT* Index2Fact(FACTOID e);
inline FACTOID currentFactIndex() { return (currentFact) ? (FACTOID)((currentFact - factBase)) : 0;}
FACT* FactTextIndex2Fact(char* word);

// fact system startup and shutdown
void InitFacts();
void CloseFacts();
void ResetFactSystem(FACT* locked);
void InitFactWords();

// fact creation and destruction
FACT* FindFact(MEANING subject, MEANING verb, MEANING object, unsigned int properties = 0);
FACT* CreateFact(MEANING subject,MEANING verb, MEANING object,unsigned int properties = 0);
FACT* CreateFastFact(MEANING subject, MEANING verb, MEANING object, unsigned int properties);
void KillFact(FACT* F);
FACT* SpecialFact(MEANING verb, MEANING object,unsigned int flags);
void FreeFact(FACT* F);
char* GetSetEnd(char* x);

// fact reading and writing
char* ReadField(char* ptr,char* field,char fieldkind,unsigned int& flags);
char* EatFact(char* ptr,unsigned int flags = 0,bool attribute = false);
FACT* ReadFact(char* &ptr);
void ReadFacts(const char* name,uint64 zone,bool user = false);
char* WriteFact(FACT* F,bool comments,char* buffer,bool ignoreDead = false,bool eol = false);
void WriteFacts(FILE* out,FACT* from);
bool ReadBinaryFacts(FILE* in);
void WriteBinaryFacts(FILE* out,FACT* F);
void ClearUserFacts();

// factset information
char* GetSetType(char* x);
int GetSetID(char* x);
bool GetSetMod(char* x);
unsigned int AddFact(unsigned int set, FACT* F);

// reading and writing facts to file
bool ExportFacts(char* name, int set,char* append);
bool ImportFacts(char* name, char* store, char* erase, char* transient);

// debugging
void TraceFact(FACT* F,bool ignoreDead = true);

// field access

inline FACT* GetSubjectHead(FACT* F) {return Index2Fact(F->subjectHead);}
inline FACT* GetVerbHead(FACT* F) {return Index2Fact(F->verbHead);}
inline FACT* GetObjectHead(FACT* F) {return Index2Fact(F->objectHead);}
inline void SetSubjectHead(FACT* F, FACT* value){ F->subjectHead = Fact2Index(value);}
inline void SetVerbHead(FACT* F, FACT* value) {F->verbHead = Fact2Index(value);}
inline void SetObjectHead(FACT* F, FACT* value){ F->objectHead = Fact2Index(value);}

inline FACT* GetSubjectNext(FACT* F) { return Index2Fact(F->subjectNext);}
inline FACT* GetVerbNext(FACT* F) {return Index2Fact(F->verbNext);}
inline FACT* GetObjectNext(FACT* F) {return Index2Fact(F->objectNext);}
inline void SetSubjectNext(FACT* F, FACT* value){ F->subjectNext = Fact2Index(value);}
inline void SetVerbNext(FACT* F, FACT* value) {F->verbNext = Fact2Index(value);}
inline void SetObjectNext(FACT* F, FACT* value){ F->objectNext = Fact2Index(value);}

inline FACT* GetSubjectHead(WORDP D) {return Index2Fact(D->subjectHead);}
inline FACT* GetVerbHead(WORDP D) {return Index2Fact(D->verbHead);}
inline FACT* GetObjectHead(WORDP D)  {return Index2Fact(D->objectHead);}
inline void SetSubjectHead(WORDP D, FACT* value) {D->subjectHead = Fact2Index(value);}
inline void SetVerbHead(WORDP D, FACT* value) {D->verbHead = Fact2Index(value);}
inline void SetObjectHead(WORDP D, FACT* value) {D->objectHead = Fact2Index(value);}

inline FACT* GetSubjectHead(MEANING M) {return GetSubjectHead(Meaning2Word(M));}
inline FACT* GetVerbHead(MEANING M) {return GetVerbHead(Meaning2Word(M));}
inline FACT* GetObjectHead(MEANING M)  {return GetObjectHead(Meaning2Word(M));}
inline void SetSubjectHead(MEANING M, FACT* value) {SetSubjectHead(Meaning2Word(M),value);}
inline void SetVerbHead(MEANING M, FACT* value) {SetVerbHead(Meaning2Word(M),value);}
inline void SetObjectHead(MEANING M, FACT* value) {SetObjectHead(Meaning2Word(M),value);}

#endif
