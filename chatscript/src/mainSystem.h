﻿﻿﻿#ifndef MAINSYSTEMH
#define MAINSYSTEMH
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

#define ID_SIZE 500
#define OUTPUT_BUFFER_SIZE 20000

typedef struct RESPONSE
{
    unsigned int responseInputIndex;                        // which input sentence does this stem from?
	unsigned int topic;										// topic of rule
	char id[24];											// .100.30
 	char relayid[24];										// 324.100.30 topic and rule doing relay
	char response[OUTPUT_BUFFER_SIZE];						// answer sentences, 1 or more per input line
} RESPONSE;


#define MAX_RESPONSE_SENTENCES 20
#define MAX_SENTENCE_LENGTH 256 // room for +2 after content 
#define REAL_SENTENCE_LIMIT 253 // stay under char size boundary (including +1)

#define BIG_WORD_SIZE   10000
#define MAX_WORD_SIZE   1500       
#define MAX_MESSAGE     1500

#define START_BIT 0x8000000000000000ULL	// used looping thru bit masks

// values of prepareMode
 enum PrepareMode { // how to treat input
	NO_MODE = 0,				// std processing of user inputs
	POS_MODE = 1,				// just pos tag the inputs
	PREPARE_MODE = 2,			// just prepare the inputs
	POSVERIFY_MODE = 4,
	POSTIME_MODE = 8,
	PENN_MODE = 16,
	REGRESS_MODE = 32,			// inputs are from a regression test
};

 enum RegressionMode { 
	NO_REGRESSION = 0,
	NORMAL_REGRESSION = 1,
	REGRESS_REGRESSION = 2,
};

// values of echoSource
 enum EchoSource {
	NO_SOURCE_ECHO = 0,
	SOURCE_ECHO_USER = 1,
	SOURCE_ECHO_LOG = 2,
};

extern clock_t startTimeInfo;
extern unsigned int outputLength;
extern bool readingDocument;
extern unsigned char responseOrder[MAX_RESPONSE_SENTENCES+1];
extern RESPONSE responseData[MAX_RESPONSE_SENTENCES+1];
extern unsigned int responseIndex;
extern bool documentMode;
extern unsigned int inputCount;
extern FILE* sourceFile;
extern unsigned long sourceStart;
extern unsigned int sourceTokens;
extern unsigned int sourceLines;
extern char* version;
extern unsigned int tokenCount;
extern unsigned int choiceCount;

extern int inputCounter,totalCounter;
extern unsigned int inputSentenceCount;  
extern char* extraTopicData;
extern char* postProcessing;
extern uint64 tokenControl;
extern bool moreToCome,moreToComeQuestion;
extern unsigned int trace;
extern int regression;
extern EchoSource echoSource;
extern bool all;
extern PrepareMode prepareMode;
extern PrepareMode tmpPrepareMode;
extern unsigned int startSystem;
extern char oktest[MAX_WORD_SIZE];
extern bool autonumber;
extern bool showWhy;
extern bool showTopic;
extern bool showInput;
extern bool showReject;
extern bool showTopics;
extern bool shortPos;
extern char users[100];
extern char logs[100];

// pending control
extern int systemReset;
extern bool quitting;
extern bool unusedRejoinder;

extern bool noReact;

// server
extern unsigned int port;
extern bool server;
#ifndef DISCARDSERVER
extern std::string interfaceKind;
#endif

// buffers
extern char mainInputBuffer[MAX_BUFFER_SIZE];
extern char mainOutputBuffer[MAX_BUFFER_SIZE];
extern char currentInput[MAX_BUFFER_SIZE];
extern char revertBuffer[MAX_BUFFER_SIZE];
extern char* readBuffer;
extern char* nextInput;

extern char activeTopic[200];

extern int always; 
extern unsigned int callBackTime;
extern unsigned int callBackDelay;
extern unsigned int loopBackTime;
extern unsigned int loopBackDelay;
extern unsigned int alarmTime;
extern unsigned int alarmDelay;

void ProcessInputFile();
bool ProcessInputDelays(char* buffer,bool hitkey);

// startup
#ifdef DLL
extern "C" __declspec(dllexport) unsigned int InitSystem(int argc, char * argv[],char* unchangedPath = NULL,char* readonlyPath = NULL, char* writablePath = NULL);
#else
unsigned int InitSystem(int argc, char * argv[],char* unchangedPath = NULL,char* readonlyPath = NULL, char* writablePath = NULL);
#endif

void InitStandalone();
void CreateSystem();
void ReloadSystem();
void CloseSystem();
void ReadParams();
int main(int argc, char * argv[]);
void ProcessOOB(char* buffer);
void ComputeWhy(char* buffer);

// Input processing
void MainLoop();
void FinishVolley(char* input,char* output,char* summary);
unsigned int ProcessInput(char* input,char* output);
void DoSentence(char* prepassTopic);
#ifdef DLL
extern "C" __declspec(dllexport) int PerformChat(char* user, char* usee, char* incoming,char* ip,char* output);
extern "C" __declspec(dllexport) int PerformChatGivenTopic(char* user, char* usee, char* incoming,char* ip,char* output,char* topic);
#else
int PerformChat(char* user, char* usee, char* incoming,char* ip,char* output);
int PerformChatGivenTopic(char* user, char* usee, char* incoming,char* ip,char* output,char* topic);
#endif
void ResetSentence();
void ResetToPreUser();
void PrepareSentence(char* input,bool mark = true,bool user=true);
bool PrepassSentence(char* presspassTopic);
int Reply();
void OnceCode(const char* var,char* topic = NULL);
void AddBotUsed(const char* reply,unsigned int len);
void AddHumanUsed(const char* reply);
bool HasAlreadySaid(char* msg);
bool AddResponse(char* msg);
char* ConcatResult();


#endif
