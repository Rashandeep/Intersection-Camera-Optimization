#include <bits/stdc++.h>
#include <time.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <string.h>
#include <errno.h>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
// #include<thread>
using namespace std;
using namespace Minisat;
vector<vector<int> >  edge_matrix;
vector<vector<int> >  dummy_edge_matrix;
vector<vector<int> >  dummy_edge_matrix1;
vector<vector<int> >  matrix;
vector<vector<int> >  matrix1;
vector<vector<int> >  dummy_egde_for_cnf;
vector<vector<int> >  dummy_egde_for_cnf_3;
pthread_t IOthread, thread2,cnfthread,algo2threadd,algo3threadd, algo2optithreadd, algo3optithreadd;
clockid_t cid1,cnf3time,algo2time,algo3time,algo2o,algo3o;
bool flagcnf=1,flag3cnf=1;
vector<int> ans1;
vector<int> algo2,algo3;
vector<int> mostOpti1, mostOpti2;

#define handle_error(msg) \
               do { perror(msg); exit(EXIT_FAILURE); } while (0)

#define handle_error_en(en, msg) \
               do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

string delimiter = ",";
vector<int> ans;

string line=" ";

vector<int> cnftimevec, threecnftimevec, algo2timevec, algo3timevec, algo2optitimevec, algo3optitimevec;

static void pclock(char *msg, clockid_t cid)
{
	struct timespec ts;

	printf("%s", msg);
	if (clock_gettime(cid, &ts) == -1)
		handle_error("clock_gettime");
//    printf("%d\n", (intmax_t) ts.tv_sec/1000000000);
//    cout<<ts.tv_sec/float(1000000000000000)<<endl;
//    cout<<ts.tv_sec<<endl;
printf("%4jd.%03ld\n", (intmax_t) ts.tv_sec, ts.tv_nsec / 1000000);
//    printf("%jd.%09ld\n", (intmax_t) ts.tv_sec, ts.tv_nsec);
}
vector<string> getSubs(string str) {
    int x = 0;
    string delimiter1 = "<";
	string delimiter2 = ">";
	vector<string> substrs;
    size_t position = str.find(delimiter1);
    stack<int> stack;
    stack.push(x);
    stack.push(x+1);
    stack.push(x+2);
	while (position != string::npos) {
    	int y;
    	size_t endPos; 
        endPos = str.find(delimiter2, position);
        y = 1;
        if (str.find(delimiter2, position) == string::npos) break;
        int a = position + 1;
        int b = endPos - position - 1;
        substrs.push_back(str.substr(a, b));
        y = 0;
        position = str.find('<', endPos);
    }
    while (!stack.empty()) {
        stack.pop();
    }
    x = 0;
    return substrs;
}
// void makeLiteralMatrix(Minisat::Lit** literal_matrix, int vertex){
// 	for(int i=0;i<vertex;i++){
// 		for(int j=0;j<vertex;j++){
// 			literal_matrix[i][j] = Minisat::mkLit(solver->newVar());
// 		}
// 	}
// }

// bool checkIfItisVertexCover(vector<int> currentV, vector<vector<int>> matrix){
// 	unordered_map<int,int> allVertices;
// 	for(int i=0;i<currentV.size();i++){
// 		allVertices[currentV[i]]=1;
// 	}
// 	for(int i=0;i<matrix.size();i++)
// 	for(int j=0;j<matrix[0].size();j++){
// 		if(matrix[i][j]==1 && (allVertices.find(i)!=allVertices.end() || allVertices.find(j)!=allVertices.end())){
//             continue;
// 		}
// 		else if(matrix[i][j]==1)
// 		return false;
// 	}
// 	return true;
// }

// void recurisveOpti(vector<int> origV, vector<int> currentV, int i, int &optimal,vector<vector<int> >  matrix, vector<int> &mostOpti){

// 	if(i==origV.size())
// 	{int currentSize=currentV.size();
// 		//check if it is still a vertex cover
//         if(checkIfItisVertexCover(currentV,matrix))
// 		 if(optimal>currentSize)
// 		  {mostOpti=currentV;optimal=currentSize;}
// 		return;
// 	}
// 	vector<int> case1;
// 	case1=currentV;
// 	case1.push_back(origV[i]);
// 	recurisveOpti(origV,case1,i+1,optimal,matrix,mostOpti);
// 	recurisveOpti(origV,currentV,i+1,optimal,matrix,mostOpti);

// }

void three_cnf(){
	// new algo
	int vertex = dummy_egde_for_cnf_3.size();
				
                // vec<Lit>  vector_Lists;
				// cout << "after solver1";
				
				for(int top=0;top<vertex;top++){
					std::unique_ptr<Minisat::Solver> solver1(new Minisat::Solver());
                    Lit literal_matrix[vertex][vertex];
					for(int i=0;i<vertex;i++){
                        for(int j=0;j<vertex;j++){
                            literal_matrix[i][j] = mkLit(solver1->newVar());
                        }
                    }

					// cout << "before of 1st clause";
					for(int k=0;k<=top;k++){
						Lit freeLiterals[vertex];
						for(int iii=0;iii<vertex;iii++){
							freeLiterals[iii] = mkLit(solver1->newVar());
						}
                        // vector_Lists.clear();
						for(int v=0;v<vertex;v++){
							if(v==0)
								solver1->addClause(literal_matrix[v][k], freeLiterals[v]);
							else if (v==vertex-1)
								solver1->addClause(~freeLiterals[v-1], literal_matrix[v][k]);
							else
								solver1->addClause(~freeLiterals[v-1], literal_matrix[v][k], freeLiterals[v]);
							// vector_Lists.push(literal_matrix[v][k]);
						}
						// solver->addClause(vector_Lists);
						
					}

					// cout << "out of 1st clause";
					
					for(int i=0;i<vertex;i++){
						for(int j=0;j<=top;j++){
							for(int a = j+1;a<=top;a++){
								solver1->addClause(~literal_matrix[i][j], ~literal_matrix[i][a]);
							}
						}
						
					}
					
					for(int i=0;i<=top;i++){
						for(int j=0;j<vertex;j++){
							for(int a = j+1;a<vertex;a++){
								solver1->addClause(~literal_matrix[j][i], ~literal_matrix[a][i]);
							}
						}
						
					}
					
					// vec<Lit>  vector_Lists_for_fourth;
					int row1 = dummy_egde_for_cnf_3.size();
					int col1 = dummy_egde_for_cnf_3[0].size();
					for(int i=0;i<row1;i++){
						for(int j=0;j<col1;j++){
							// vector_Lists_for_fourth.clear();
							if(dummy_egde_for_cnf_3[i][j]==1){
								dummy_egde_for_cnf_3[j][i] = 0;
								Lit freeLiterals[vertex*2];
								for(int iii=0;iii<vertex*2;iii++){
									freeLiterals[iii] = mkLit(solver1->newVar());
								}
								int dum = 0;
								// // cout << top << endl;
								for(int a = 0;a<=top;a++){	
									if (a==0 && top!=0){
										// cout << "1st" << endl;
										// cout << dum << endl;
										solver1->addClause(literal_matrix[i][a],freeLiterals[dum]);
										solver1->addClause(~freeLiterals[dum],literal_matrix[j][a],freeLiterals[dum+1]);
										dum++;
										// cout << dum << endl;
									} 
									else if (a==0 && top==0){
										// cout << "2st" << endl;
										solver1->addClause(literal_matrix[i][a],freeLiterals[dum]);
										solver1->addClause(~freeLiterals[dum],literal_matrix[j][a]);
									}
									else if (a==top){
										// cout << "3st" << endl;
										// cout << dum << endl;
										solver1->addClause(~freeLiterals[dum],literal_matrix[i][a],freeLiterals[dum+1]);
										dum++;
										solver1->addClause(~freeLiterals[dum],literal_matrix[j][a]);
										// cout << dum << endl;
									} else {
										// cout << "4st" << endl;
										solver1->addClause(~freeLiterals[dum],literal_matrix[i][a],freeLiterals[dum+1]);
										dum++;
										solver1->addClause(~freeLiterals[dum],literal_matrix[j][a], freeLiterals[dum+1]);
										dum++;
										// dum++;
									}
									// cout << "one for loop is over with value of a " << a << endl;
									// dum++;
									// vector_Lists_for_fourth.push(literal_matrix[i][a]);
									// vector_Lists_for_fourth.push(literal_matrix[j][a]);
								}
								// solver1->addClause(vector_Lists_for_fourth);
								// cout << "out of for loop" << endl;
							}
						}
					}
					// cout<<"before solve "<<endl;
					// continue;
					bool res = solver1->solve();


					// for(int i=0;i<vertex;i++){
					// 	for(int j=0;j<vertex;j++){
					// 		lbool iss = solver1->modelValue(literal_matrix[i][j]);
					// 		if(iss == l_True){
					// 			cout << "1" << " ";
					// 		}
					// 		else{
					// 			cout << "0"<< " ";
					// 		}
					// 	}
					// 	cout << "\n";
					// }

					// cout << "after solve" << endl;
					if(res){
						ans1.clear();
						for(int i=0;i<vertex;i++){
							for(int j=0;j<=top;j++){
								lbool iss = solver1->modelValue(literal_matrix[i][j]);
								if(iss == l_True){
									ans1.push_back(i);
								}
							}
						}
            			break;
					}
					else{
						solver1.reset (new Solver());
					}	
				}
}

void cnf(){
	int vertex =  dummy_egde_for_cnf.size();
	
                vec<Lit>  vector_Lists;
				int arr[100];
				// Minisat::Lit literal_matrix[vertex][vertex];
				// for(int i=0;i<vertex;i++){
				// 	for(int =0;j<vertex;j++){
				// 		literal_matrix[i][j] = Minisat::mkLit(solver->newVar());
				// 	}
				// }
				
				for(int top=0;top<vertex;top++){
					std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
					// cout<<"top == "<<top<<endl;
					// int** literal_matrix = new Minisat::Lit*[vertex];
				    // for (int i = 0; i < vertex; i++) {
				    //     literal_matrix[i] = new int[vertex];
				    // }
					
					// makeLiteralMatrix(literal_matrix, vertex);
                    Lit literal_matrix[vertex][vertex];
                    
					for(int i=0;i<vertex;i++){
                        for(int j=0;j<vertex;j++){
                            literal_matrix[i][j] = mkLit(solver->newVar());
                        }
                    }
					
					stack<int> covered;
					for(int k=0;k<=top;k++){
                        vector_Lists.clear();
						covered.push(k);
						for(int v=0;v<vertex;v++){
							arr[0] = v;
							vector_Lists.push(literal_matrix[v][k]);
							arr[1] = v+1;

							vector<vector<int>> intervals{{1,2},{3,4}};
							unordered_map<int,int> map;
							for(int i=0;i<intervals.size();i++){
								for(auto it:map){
									if(it.first>=intervals[i][0]){
										if (intervals[i][1]>intervals[it.second][1])
											swap(intervals[it.second][1],intervals[i][1]);
										intervals.erase( intervals.begin() + i);
										i--;
										map.erase(it.first);
										break;
									}
								}
								map[intervals[i][1]] = i;
							}
						}
						solver->addClause(vector_Lists);
						covered.push(arr[0]);
					}
					
					for(int i=0;i<vertex;i++){
						covered.push(i);
						for(int j=0;j<=top;j++){
							for(int a = j+1;a<=top;a++){
								int xx,yy,zz;
								xx = top;
								for (int q = 0;q<xx;q++){
									if (q%2==0){
										yy++;
										zz--;
									}
									else{
										zz++;
										yy--;
									}
								}
								arr[2] = a;
								arr[3] = a+1;
								solver->addClause(~literal_matrix[i][j], ~literal_matrix[i][a]);
							}
						}
						covered.push(arr[2]);
					}
					
					for(int i=0;i<=top;i++){
						for(int j=0;j<vertex;j++){
							for(int a = j+1;a<vertex;a++){
								arr[3] = i;
								arr[2] = i+1;
								vector<int> ttt{0,1,2};
								int maxi = 0;
								for (int w = 0;w<ttt.size();w++){
									int sum = ttt[0];
									if(sum<0){
										sum = 0;
									}
									int maxi= max(sum,maxi);
									if(sum>0){
										sum = ttt[1];
									} 
								}
								solver->addClause(~literal_matrix[j][i], ~literal_matrix[a][i]);
							}
						}
						covered.push(arr[3]);
					}
					
					vec<Lit>  vector_Lists_for_fourth;
					int row1 = dummy_egde_for_cnf.size();
					int col1 = dummy_egde_for_cnf[0].size();
					for(int i=0;i<row1;i++){
						for(int j=0;j<col1;j++){
							vector_Lists_for_fourth.clear();
							if(dummy_egde_for_cnf[i][j]==1){
								for(int a = 0;a<=top;a++){
									vector_Lists_for_fourth.push(literal_matrix[i][a]);
									vector_Lists_for_fourth.push(literal_matrix[j][a]);
								}
								solver->addClause(vector_Lists_for_fourth);
							}
						}
					}
					// cout<<"before solve "<<endl;
					// continue;
					bool res = solver->solve();
					// cout << "after solve" << endl;
					if(res){
						ans.clear();
						for(int i=0;i<vertex;i++){
							for(int j=0;j<=top;j++){
								while(!covered.empty()){
									covered.pop();
									arr[0] = i;
									arr[1] = j;
								}
								lbool iss = solver->modelValue(literal_matrix[i][j]);
								if(iss == l_True){
									ans.push_back(i);
								}
							}
						}
            			break;
					}
					else{
                        // cout << "the ans is not given" << endl;
						solver.reset (new Solver());
					}	
				}
}


vector<int> algoFun2(){
					int row = dummy_edge_matrix.size();
				int col = dummy_edge_matrix[0].size();

				// for (int i=0;i<row;i++){
				// 	for(int j=0;j<col;j++){
				// 		cout << dummy_edge_matrix[i][j] << " ";
				// 	}
				// 	cout << "\n";
				// }

				vector<int> noOfOnes;
				vector<int> algo2;
				for (int i=0;i<row;i++){
					int count = 0;
					for(int j=0;j<col;j++){
						if(dummy_edge_matrix[i][j]==1){
							count++;
						}
					}
					noOfOnes.push_back(count);
				}
				
				// for (int i=0;i<noOfOnes.size();i++){
				// 	cout << noOfOnes[i] << " ";
				// }
				// cout << "\n";
				

				int maxElement = 0;
				while(true){
					int maxElement = *std::max_element(noOfOnes.begin(), noOfOnes.end());
					if(maxElement==0){
						break;
					}
					
					int maxElementIndex = std::max_element(noOfOnes.begin(),noOfOnes.end()) - noOfOnes.begin();
					algo2.push_back(maxElementIndex);

					// int minElementIndex = std::min_element(noOfOnes.begin(),noOfOnes.end()) - noOfOnes.begin();
					// int minElement = *std::min_element(noOfOnes.begin(), noOfOnes.end());

					// cout << maxElement << " index " << maxElementIndex << endl;
					// cout << minElement << " index " << minElementIndex << endl;

					for(int j=0;j<col;j++){
						if(dummy_edge_matrix[maxElementIndex][j]==1){
							dummy_edge_matrix[maxElementIndex][j]=0;
							dummy_edge_matrix[j][maxElementIndex]=0;
						}
					}
					noOfOnes[maxElementIndex] = 0;
					noOfOnes.clear();
					for (int i=0;i<row;i++){
						int count = 0;
						for(int j=0;j<col;j++){
							if(dummy_edge_matrix[i][j]==1){
								count++;
							}
						}
						noOfOnes.push_back(count);
					}

				}
				sort(algo2.begin(),algo2.end());

return algo2;
}

vector<int> algoFun3(){
	int row = dummy_edge_matrix1.size();
				int col = dummy_edge_matrix1[0].size();
					vector<int> algo3;
				for(int i=0;i<row;i++){
					for(int j=0;j<col;j++){
						if(dummy_edge_matrix1[i][j]==1){
                   if (find(algo3.begin(), algo3.end(), i) == algo3.end())
								algo3.push_back(i);
							if (find(algo3.begin(), algo3.end(), j) == algo3.end())
								algo3.push_back(j);
							for(int k=0;k<col;k++){
								if(dummy_edge_matrix1[i][k]==1){
									dummy_edge_matrix1[i][k] = 0;
									dummy_edge_matrix1[k][i] = 0;
								}
								if(dummy_edge_matrix1[j][k]==1){
									dummy_edge_matrix1[j][k] = 0;
									dummy_edge_matrix1[k][j] = 0;
								}
							}
						}
					}
				}
				sort(algo3.begin(),algo3.end());
	return algo3;
}

// void algo2Optimise(vector<int> algo2){
// 				// vector<int> newVertexCover1;
// 				// int optimal1=INT_MAX;
// 				// recurisveOpti(algo2,newVertexCover1,0,optimal1,matrix1,mostOpti1);


// }

// void algo3Optimise(vector<int> algo3){
// 				// 	vector<int> newVertexCover;
// 				// int optimal=INT_MAX;
// 				// recurisveOpti(algo3,newVertexCover,0,optimal,matrix,mostOpti2);
// 				// cout<<"this is algo 3 optimal solution "<<endl;



// }

void algo2Optimise(vector<int> algo2){
	// cout<<"starting algo2optimise";
	mostOpti1.clear();
	vector<int> degg;
	unordered_map<int,int> algo3loc;
	for(int i=0;i<algo2.size();i++)
	algo3loc[algo2[i]]++;
					vector<int> newVertexCover;
				int optimal=INT_MAX;
				while(1){
				for(int i=0;i<matrix.size();i++)
				{int count=0;for(int j=0;j<matrix[i].size();j++){
                              if(matrix[i][j])count++;
				}degg.push_back(count);}
				int maxElement = *std::max_element(degg.begin(), degg.end());
				// 				for(int i=0;i<degg.size();i++)
				// cout<<degg[i]<<" ";cout<<endl;
				if(maxElement)
				{int maxElementIndex = std::max_element(degg.begin(),degg.end()) - degg.begin();
				newVertexCover.push_back(maxElementIndex);
				if(algo3loc.find(maxElementIndex)!=algo3loc.end())
				{
                   for(int i=0;i<matrix[maxElementIndex].size();i++)
				   {if(matrix[maxElementIndex][i] && algo3loc.find(i)!=algo3loc.end()){
					int cc=0;
					for(int qq=0;qq<matrix[i].size();qq++){
                        if(matrix[i][qq] && algo3loc.find(qq)==algo3loc.end())
						cc=1;
					}
					if(!cc)
					algo3loc.erase(i);
					matrix[maxElementIndex][i]=0;matrix[i][maxElementIndex]=0;
				   }
				   else if(matrix[maxElementIndex][i])
				   {matrix[maxElementIndex][i]=0;
				   matrix[i][maxElementIndex]=0;}}
				}
				else {
					for(int i=0;i<matrix[maxElementIndex].size();i++)
				   if(matrix[maxElementIndex][i])
				  { matrix[maxElementIndex][i]=0;matrix[i][maxElementIndex]=0;}
				}
				}
				else
				break;
				degg.clear();
				}

				mostOpti1=newVertexCover;
				sort(mostOpti1.begin(),mostOpti1.end());
				// vector<int> newVertexCover1;
				// int optimal1=INT_MAX;
				// recurisveOpti(algo2,newVertexCover1,0,optimal1,matrix1,mostOpti1);
}

void algo3Optimise(vector<int> algo3){
	// ohhh=0;
	mostOpti2.clear();
	unordered_map<int,int> algo3loc;
	for(int i=0;i<algo3.size();i++)
	algo3loc[algo3[i]]++;
					vector<int> newVertexCover;
					vector<int> degg;
				int optimal=INT_MAX;
				while(1){
				for(int i=0;i<matrix1.size();i++)
				{int count=0;for(int j=0;j<matrix1[i].size();j++){
                              if(matrix1[i][j])count++;
				}degg.push_back(count);}
				int maxElement = *std::max_element(degg.begin(), degg.end());
				// for(int i=0;i<degg.size();i++)
				// cout<<degg[i]<<" ";cout<<endl;
				if(maxElement)
				{
				int maxElementIndex = std::max_element(degg.begin(),degg.end()) - degg.begin();
				// cout<<"this is index "<<maxElementIndex<<endl;
				newVertexCover.push_back(maxElementIndex);
				if(algo3loc.find(maxElementIndex)!=algo3loc.end())
				{
                   for(int i=0;i<matrix1[maxElementIndex].size();i++){
				   if(matrix1[maxElementIndex][i] && algo3loc.find(i)!=algo3loc.end()){
					int cc=0;
					for(int qq=0;qq<matrix[i].size();qq++){
                        if(matrix1[i][qq] && algo3loc.find(qq)==algo3loc.end())
						cc=1;
					}
					if(!cc)
					algo3loc.erase(i);
					matrix1[maxElementIndex][i]=0;matrix1[i][maxElementIndex]=0;
				   }
				   else if(matrix1[maxElementIndex][i])
				  { matrix1[maxElementIndex][i]=0;
				  matrix1[i][maxElementIndex]=0;}}
				}
				else {
					for(int i=0;i<matrix1[maxElementIndex].size();i++)
				   if(matrix1[maxElementIndex][i])
				  { matrix1[maxElementIndex][i]=0;matrix1[i][maxElementIndex]=0;}
				}
				}
				else
				break;
				degg.clear();
				}

				mostOpti2=newVertexCover;
				sort(mostOpti2.begin(),mostOpti2.end());
				// cout<<"this is algo 3 optimal solution "<<endl;
}

       static void *
       threeCnfThreadfn(void *arg)
       {
        //    printf("going to execute three cnf thread");
		//    cout<<endl;
           three_cnf();
		//    cout<<"done wih 3cnf";
		//    cout<<endl;
		// 	pthread_getcpuclockid(thread2,&cid1);

		//    pclock("CNF-3-SAT-VC: thread time ", cid1);
		//    threecnftimevec.push_back(cid1);
		//    cout << endl;
       }

	          static void *
       CnfThreadfn(void *arg)
       {
		// int yy;
        //    printf("going to execute cnf thread");cout<<endl;
           cnf();
		//    cout<<"don with cnf";
		//    cout<<endl;
		// pthread_getcpuclockid(cnfthread,&cnf3time);
		// 	// cout << "the value of yy is " << yy << endl;
		//    pclock("CNF-SAT-VC: thread time ", cnf3time);
		//    cnftimevec.push_back(cnf3time);
		//    cout << endl;
       }



			          static void *
       algo2optithread(void *arg)
       {
		//    cout<<"starting algo2 optimise"<<endl;
		   algo2Optimise(algo2);
		//    cout<<"done withalgo2 optimise"<<endl;
		//    pthread_getcpuclockid(algo2optithreadd,&algo2o);
		//    pclock("REFINED-APPROX-VC-1: thread time    ", algo2o);
		//    algo2optitimevec.push_back(algo2o);
		//    cout << endl;
       }


	   	          static void *
       algo2thread(void *arg)
       {
        //    printf("going to execute algo2 thread");cout<<endl;
           algo2 = algoFun2();
		//    cout<<"don with algo2";
		//    cout<<endl;

		//    pthread_getcpuclockid(algo2threadd,&algo2time);
		//    pclock("APPROX-VC-1: thread time    ", algo2time);
		//    algo2timevec.push_back(algo2time);
		//    cout << endl;
		//    pthread_t algo2optithreadd;
           pthread_create(&algo2optithreadd, NULL, algo2optithread, NULL);
 			// pthread_join(algo2optithreadd, NULL);
			
		//     pthread_getcpuclockid(algo2optithreadd,&algo2o);
		//    pclock("algo2Optimise thread time    ", algo2o);

		//    cout<<"starting algo2 optimise"<<endl;
		//    algo2Optimise(algo2);
		//    cout<<"done withalgo2 optimise"<<endl;
       }

			          static void *
       algo3optithread(void *arg)
       {
		   		//    cout<<"starting algo3 optimise"<<endl;
		   algo3Optimise(algo3);
		//    cout<<"done withalgo3 optimise"<<endl;
		//    pthread_getcpuclockid(algo3optithreadd,&algo3o);
		//    pclock("REFINED-APPROX-VC-2: thread time : ", algo3o);
		//    algo3optitimevec.push_back(algo3o);
		//    cout << endl;
       }


	   	          static void *
       algo3thread(void *arg)
       {
        //    printf("going to execute algo3 thread");cout<<endl;
            algo3 = algoFun3();
		//    cout<<"don with algo3";
		//    cout<<endl;
		//    		              		   pthread_getcpuclockid(algo3threadd,&algo3time);
		//    pclock("APPROX-VC-2: thread time    ", algo3time);
		//    algo3timevec.push_back(algo3time);
		//    cout << endl;
		   		//    pthread_t algo3optithreadd;

// time_t start, end;
//   time(&start);
			pthread_create(&algo3optithreadd, NULL, algo3optithread, NULL);
//  pthread_join(algo3optithreadd, NULL);
//  time(&end);


//    time(&end);
//    double time_taken = double(end - start);
//     cout << "Time taken by a3optimised is : " << fixed
//         << time_taken << setprecision(5);
//     cout << " sec " << endl;
       }
void getGraph(){
		system("/home/agurfink/ece650/graphGen/graphGen 14  >  out.txt");
}

void getcindata(){
			getline(cin,line); 
			// cout << line << endl;
}

static void *
       IOThreadFunction(void *arg)
       {
        //    printf("going to execute three cnf thread");
		//    cout<<endl;
        //    getGraph();

getcindata();

		//    cout<<"done wih 3cnf";
		//    cout<<endl;
		// 	pthread_getcpuclockid(thread2,&cid1);

		//    pclock("CNF-3-SAT-VC: thread time ", cid1);
		//    cout << endl;
       }

void printResult(){
                        int size = ans.size();
						cout << "CNF-SAT-VC: ";
						if(flagcnf)
						cout<<"timeout"<<endl;
						else{
						for(int i = 0; i < size; i++) {
							if(i==size-1)
								cout << ans[i];
							else
                				cout << ans[i] << ",";
            			}
            			cout<<endl;
						}

						int size1 = ans1.size();
						cout << "CNF-3-SAT-VC: ";
						if(flag3cnf)
						cout<<"timeout"<<endl;
						else{
						for(int i = 0; i < size1; i++) {
                			if(i==size1-1)
								cout << ans1[i];
							else
                				cout << ans1[i] << ",";
            			}
            			cout<<endl;
						}

						cout << "APPROX-VC-1: ";
						for (int i=0;i<algo2.size();i++){
							// cout << algo2[i] << " ";
							if(i==algo2.size()-1)
								cout << algo2[i];
							else
                				cout << algo2[i] << ",";
						}
						cout << "\n";

						cout << "APPROX-VC-2: ";
						for (int i=0;i<algo3.size();i++){
							// cout << algo3[i] << " ";
							if(i==algo3.size()-1)
								cout << algo3[i];
							else
                				cout << algo3[i] << ",";
						}
						cout << "\n";

						cout<<"REFINED-APPROX-VC-1: ";
						for(int i=0;i<mostOpti1.size();i++){
							if(i==mostOpti1.size()-1)
								cout << mostOpti1[i];
							else
                				cout << mostOpti1[i] << ",";
						}
						// cout<<mostOpti1[i]<<" ";
						// algo2 optimise
						cout << "\n";

						cout << "REFINED-APPROX-VC-2: ";
						for(int i=0;i<mostOpti2.size();i++)
						{
							if(i==mostOpti2.size()-1)
								cout << mostOpti2[i];
							else
                				cout << mostOpti2[i] << ",";
						}
						// cout<<mostOpti2[i]<<" ";
						cout <<endl;
}  

int main(int argc, char* argv[]){
					// char* ex = "../.././home/rbabaeec/ece650/graphGen/graphGen";
	    		// char* argument_list[] = {"../.././home/rbabaeec/ece650/graphGen/graphGen","5",NULL};
// cout<<"start time"<<endl;
//  time_t now = chrono::system_clock::to_time_t(chrono::system_clock::now());
//        cout << put_time(localtime(&now), "%F %T") <<  endl;
	    		// int sta_co = execv(ex, argument_list);

		// system("/home/agurfink/ece650/graphGen/graphGen 6  >  out.txt");

		// ifstream myfile ("out.txt");

		// pthread_create(&IOthread, NULL, IOThreadFunction, NULL);
		// pthread_join(IOthread, NULL);

		// getGraph();
		// ifstream myfile ("out.txt");

		while(!cin.eof()){
			flagcnf=1;flag3cnf=1;
			// string line=" ";
			// // cout<<"WAIRING FOR LINE\n";
			// getline(cin,line); 
			// // cout << line << endl;
	        
			// getcindata();
			pthread_create(&IOthread, NULL, IOThreadFunction, NULL);
			pthread_join(IOthread, NULL);
			istringstream input(line);
			int vertex;
			if (line[0]=='V'){
				stringstream q1;
				if (line.length()==3){
		        q1 << line[2];
		        q1 >> vertex;
		    }
		    else if (line.length()==4){
		    	q1 << line.substr(2, 2);
		    	q1 >> vertex;
			}
			else {
				q1 << line.substr(2, 3);
		    	q1 >> vertex;	
			}	
			continue;
			}
	        
	        string edges;
	        string path;
	        int source;
	        int destination;
	        
			if (line[0]=='E'){
				if (vertex == 7000)
				{
					cout << "Error: Please enter vertices" << endl;
					continue;
				}
		        edge_matrix.clear();
				edges = line.substr(2,line.length());
                // cout << vertex << endl;
				// cout << edges << endl;
				for(int a = 0; a < vertex; a++)
		        {
		        	vector<int> temp;
		        	for(int b = 0; b < vertex; b++)
		        	{
		                temp.push_back(0);
		        	}
		        	edge_matrix.push_back(temp);
		        }
                
				// cout <<"vertex == "<< vertex;
                // cout << "after inilializing";
		        int flag = 0;
		        vector<string> substrings = getSubs(line);
				if(substrings.empty()){
					continue;
				}
				
				// for (auto &s: substrings) {
				// 	reverse(s.begin(), s.end());
				// 	cout << s << endl;
				// }
				vector<string> checkDuplicate;
				int flagForSame = 0;
				int substringsize = substrings.size(); 
				for (auto &s: substrings) {
					string dummy = s;
					if(find(checkDuplicate.begin(),checkDuplicate.end(),s) != checkDuplicate.end()){
						// cout << s << endl;
						flagForSame = 1;
						break;
					}
					else {
						checkDuplicate.push_back(s);
					}
					// reverse(s.begin(), s.end());
					// if (dummy == s){
					// 	continue;
					// }
					// if(find(checkDuplicate.begin(),checkDuplicate.end(),s) != checkDuplicate.end()){
					// 	// cout << s << endl;
					// 	flagForSame = 1;
					// 	break;
					// }
					// else {
					// 	checkDuplicate.push_back(s);
					// }
				}
				if(flagForSame==1){
					cout << "Error: Same edge is not allowed" << endl;
					continue;
				}
				for (string s : substrings) {
				size_t position = 0;
				int chd;
				string vali;
				chd = 0;
				string v1;
			    while ((position = s.find(delimiter)) != std::string::npos) {
			    vali = s.substr(0, position);
			    v1 = vali;
			    s.erase(0, position + delimiter.length());
				}
				string v2 = s;
				
				stringstream st;
		        st << v1;
		        int v1i;
		        st >> v1i;
				// v1i--;
		        // v1i--;
		        stringstream st1;
			    st1 << v2;
			    int v2i;
			    st1 >> v2i;
				// v2i--;
				// v2i--;
		        if (v1i>vertex-1 || v2i>vertex-1){
					flag = 1;
		        } else{
		            edge_matrix[v1i][v2i] = 1;
		            edge_matrix[v2i][v1i] = 1;
		    	}
					
    			}
		        if (flag == 1){
		        	cout << "Error: The vertex for the edge provided does not exists" <<endl;
		        	vertex = 7000;
		        	continue;	
				}
				
                // std::cout << "starting sat " << vertex << endl;
				
                dummy_edge_matrix = edge_matrix;
				dummy_edge_matrix1 = edge_matrix;
				matrix = edge_matrix;
				matrix1 = edge_matrix;
				dummy_egde_for_cnf = edge_matrix;
				dummy_egde_for_cnf_3 = edge_matrix;
           int s;
  //cout<<"current size "<<ans.size()<<" "<<ans1.size()<<endl;
  ans1.clear();ans.clear();
  //cout<<"current size "<<ans.size()<<" "<<ans1.size()<<endl;

           s = pthread_create(&thread2, NULL, threeCnfThreadfn, NULL);
		   pthread_create(&cnfthread, NULL, CnfThreadfn, NULL);
		   int waitIter;
		  // cout<<"current size "<<ans.size()<<" "<<ans1.size()<<endl;
	 flagcnf=1;flag3cnf=1;
for( waitIter=0;waitIter<30000;waitIter++)
{if(ans.size())
flagcnf=0;
if(ans1.size())
flag3cnf=0;
if(!flagcnf && !flag3cnf)
break;
else
{usleep(10000);}
}
// if(waitIter==2){
// 	cout<<"killed"<<endl;
// 	pthread_kill(cnfthread, 0);
// 	pthread_kill(thread2, 0);
// }

				
				// first.join();
				
				// three_cnf(vertex, dummy_egde_for_cnf_3);

				// cnf(vertex, dummy_egde_for_cnf);

				// algorithm -2
				pthread_create(&algo2threadd, NULL, algo2thread, NULL);

				// pthread_join(algo2threadd, NULL);

				pthread_create(&algo3threadd, NULL, algo3thread, NULL);
				if(!flagcnf)
				pthread_join(thread2, NULL);
				if(!flag3cnf)
				pthread_join(cnfthread, NULL);
				pthread_join(algo2threadd, NULL);
				pthread_join(algo3threadd, NULL);
				pthread_join(algo2optithreadd, NULL);
				pthread_join(algo3optithreadd, NULL);
				
               if(flagcnf)
			   ans.clear();
			   if(flag3cnf)
			   ans1.clear();
			
				printResult();
			// 	// algo - 3
            //    vector<int> algo3 = algoFun3(dummy_edge_matrix1);

			// 	// algo2 optimise
			// 	algo2Optimise(algo2);

			// 	//algo3 optimise
			// 	algo3Optimise(algo3);
				
				continue;
		}
			
		if(input.eof()){
			break;
		}
		continue;
	}
	
}