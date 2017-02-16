/*
 A simple implementation of Belief Propagation.
 Using adjacency list to store the graph (for undirected graph). Here, we combine two adjacency list (adjacency list and
 inverse adjacency list) into one, called orthogonal list. It's convenient to get the in degree and 
 out degree of every vertex

 TODO 
	1. Add timer
	2. add Optimazation (from the paper)
	3. Fix the file creation without permission to read

 @author: gbtux (gbtju85@gmail.com)
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <fcntl.h>
#include <time.h>
#include <math.h>
//#include <float.h>

/* debug switch*/
//#define DEBUG
#define DEBUG_TIMER_EACH_ITER

//#define BP_ITER 15   	//maximum iterations of BP
int BP_ITER = 15;   	//maximum iterations of BP
//#define MSG_MINI_THRESHOLD 0.0000000001	//when the message doesn't change significantly between iterations, BP can stop.
//#define MSG_MINI_THRESHOLD 0.005
#define MSG_MINI_THRESHOLD 0.00001
//#define ALPHA 0.7	//message damping. from HP paper
//#define ALPHA 0.3
//#define MIN_SMALL 0.00000000000000000001
//#define MIN_SMALL 1.0e-323

//(maximum degree: 1.0e-322 --> 1068, 1.0e-323 --> 1071 or 1072)
#define MIN_SMALL 1.0e-322
#define MAX_LEN 1067	//this value may not be fixed in different environment

#define FACTOR 1.0e+300

#define BUF_MAX_LEN 10240

char *outputfile = "graph_bp_result.txt";
char *outputdegree = "graph_degree.txt";

int NUM_NODES;		//num of the nodes in graph
int NUM_STATES;		//num of possible states: such as malicious, benign
float **edge_potential;	//edge potential

//for the edge elements
struct edgeNode {
	//for edge: headV->tailV
	int tailvex;		//tail vertex Id of an edge;
	int headvex;		//vertex of an edge;

	int iter;		//in which iteration the message is (0 means initial value)
	long double *msg;	//message at interation iter (NUM_STATES)
	//hold the prior message to calculate the message
	long double *msg_prior;	//message at interation iter-1 (NUM_STATES)

	//float weigth;		//reserve for weight
	//struct edgeNode *next;		//pointer to the next out edge
	struct edgeNode *inlink; //pointer to the next in edge
	struct edgeNode *outlink;//pointer to the next out edge
};

//for the vertext list
struct vertexNode {
	long double *belief;		//each node has NUM_STATES belief;
	int degree;			//node degree;
	int msg_fact;			//equal to floor(degree/MAX_LEN)
	//struct edgeNode *firstedge; 	//first out edge of this vertex
	struct edgeNode *first_in;	//first in edge of this vertex
	struct edgeNode *first_out; 	//first out neighbor(edge) of this vertex
} *AdjList;

//for pruning graph. initial value: label = -1, traveled: label = 0;
//cut: label = 1
int *label;

//clock_t start, end;
//start = clock();//or time(&start);  
//bp_alg();
//end = clock();
//printf("BP running time=%f\n", (double)(end-start)/CLOCKS_PER_SEC);


int init_graph();
void print_graph();
void print_node_belief();
void print_node_message();
int init_edge_potential();
void print_edge_potential();
void print_initial_value();
struct edgeNode* get_edgenode(int tailvex, int headvex);
int read_graph(char* graph_nodes_file, char* graph_edges_file) ;
int read_edge_potential(char* ep_file);
long double msg(int node_i, int node_j, int state, int iter);
void bp_alg();
void print_node_belief_write_file(char *filepath);
int pruning_graph();
void print_pruning_flag();
void print_degree();
void print_degree_and_write_file(char *filepath);
//int find_edgenode(int i, int vexid, struct edgeNode** ednode);


int write_file(char* filename, char* buf){
	int openfile_flag;
	int fd;

        //openfile_flag = O_CREAT|O_RDWR|O_TRUNC;	 //Overwrite mode
	openfile_flag = O_CREAT|O_RDWR|O_APPEND; //Append mode
	if((fd=open(filename, openfile_flag, 0644)) < 0){
		printf("open %s failed \n", filename);
		return -1;
	}

	if(write(fd,buf,strlen(buf)) < 0){
		printf("write file failed!\n");
		close(fd);
		return -1;
	}

	close(fd);
	return 0;
}


//for the HP paper
float edge_p(int s1, int s2){
	if(s1<NUM_STATES && s2<NUM_STATES){
		return edge_potential[s1][s2];
	}
	else{
		printf("***[1]Critical Error!***\n");
		return 0.0;
	}
}

//compute message that node i sends to node j
long double msg(int node_i, int node_j, int state, int iter){
	//#define DEBUG_LOCAL_MSG

	int i, s;
	long double ret_val = 0.0;
	int flag = 0;
	struct edgeNode *ednode = NULL;
	struct edgeNode *ednode2 = NULL;
	int err;

	//char debug_buf2[1024];
	int f = 0;

	//printf("[test]%d-->%d, iter=%d, state=%d\n", node_i, node_j, iter, state);
	for(s=0; s<NUM_STATES; s++){
		long double val = 0.0;
		//long double tmpval = 0.0; //only for debug
		int debug_cnt = 0;
		char debug_buf[1024];
		int fact;

		ednode = AdjList[node_i].first_in;
		fact = AdjList[node_i].msg_fact;

		val = AdjList[node_i].belief[s] * edge_p(s, state);
		if(val == 0.0){
			//for our 4 states, it's 0 for some states.
			//printf("***[2]Critical Error!***\n");
			continue;
		}
		#ifdef DEBUG_LOCAL_MSG
		printf("[*****test_belief_time_ep]val=%Lf\n", val);
		#endif

		//all the neighbers except for the node_j
		while(ednode){
			if(ednode->tailvex != node_j){
				debug_cnt ++;
				//tmpval = val;
				//printf("[test]ednode->headvex=%d\n", ednode->headvex);

				//we only use the iter-1 message to update the iter message
				if(ednode->iter == iter){
					val *= ednode->msg_prior[s];
					#ifdef DEBUG_LOCAL_MSG
					printf("val *= ednode->msg_prior[%d] *= %Lf = %Lf\n", s, ednode->msg_prior[s], val);
					#endif
				}
				else if(ednode->iter == iter-1){
					val *= ednode->msg[s];
					#ifdef DEBUG_LOCAL_MSG
					printf("val *= ednode->msg[%d] *= %Lf = %Lf\n", s, ednode->msg[s], val);
					#endif
				}
				else{
					//should never be here
					printf("Error iteration count!\n");
					return -1.0;
				}

				//printf("[test]get belief: headvex=%d\n", ednode->headvex);

				//if(val == (long double)0.0){
				if(val - (long double)MIN_SMALL < 0.0 && fact > 0){
					//val = (long double)MIN_SMALL;				
					//val = tmpval;
					fact --;
					val *= (long double)FACTOR;
					//printf("***[3]Error! Too small number*** %d-->%d: %.50Lf, %.50Lf\n", node_i, node_j, tmpval, val);

					//sprintf(debug_buf, "%d %d %d\n", node_i, node_j, debug_cnt);
					//write_file("bp_msg_cnt.txt", debug_buf);
					f = 1;
					//break;
				}
			}

			//move to next edge
			ednode = ednode->inlink;
		}
		#ifdef DEBUG_LOCAL_MSG
		printf("[test_time_msg]val=%.20Lf\n", val);
		#endif

		//debug: if debug_cnt != (AdjList[node_i].degree-1), there must be an error!
		if(f==1 && debug_cnt != (AdjList[node_i].degree-1)){
			sprintf(debug_buf, "===%d %d %d %d ====fact: %d\n", node_i, node_j, debug_cnt, AdjList[node_i].degree-1, fact);
			write_file("bp_msg_cnt.txt", debug_buf);
		}


		//make sure all the part time the same factors
		while(fact > 0){
			val *= (long double)FACTOR;
			fact--;
		}

		ret_val += val;

		//write_file("bp_msg_cnt.txt", debug_buf);
		//sprintf(debug_buf2, "aaaaa %d, %d bbbbb\n", node_i, debug_cnt);
		//write_file("bp_msg_cnt.txt", debug_buf2);
	}
	//if(f==1){
	//	sprintf(debug_buf2, "aaaaa %d bbbbb\n", node_i);
	//	write_file("bp_msg_cnt.txt", debug_buf2);
	//}

	#ifdef DEBUG_LOCAL_MSG
	printf("ret_val=%.20Lf\n", ret_val);
	#endif
	return ret_val;
}


/* belief propagation algorithm */
void bp_alg() {
	int i,t,s;
	struct edgeNode *ednode = NULL;
	struct edgeNode *ednode2 = NULL;
	long double k;
	int flag;
	long double msg_sum;
	long double msg_tmp[NUM_STATES];
	clock_t start, end;

	//update all the message
	printf("updating the message ...\n");
	for (t = 1; t <= BP_ITER; t++) {
		#ifdef DEBUG_TIMER_EACH_ITER
		start = clock();
		#endif
		printf("iter: %d\n", t);

		flag = 0;		
		for(i=0; i<NUM_NODES; i++) {
			//pruning
			//if(label[i]>0){
			//	//test
			//	//printf("[test_pruning]node: %d continue\n", i);
			//	continue;
			//}

			ednode = AdjList[i].first_out;
			while(ednode){
				//printf("test: %d, %d\n", i, ednode->headvex);
				//ednode = ednode->outlink;
				//usleep(100);
				//continue;

				//keep the prior message (at iteration t-1)
				msg_sum = 0.0;
				for(s=0; s<NUM_STATES; s++){
					msg_tmp[s] = 0.0;

					msg_tmp[s] = msg(i, ednode->headvex, s, t);
					//optimation: message damping
					//printf("msg = %Lf\n", msg_tmp[s]);
					//msg_tmp[s] = ALPHA * ednode->msg[s] + (1 - ALPHA) * msg_tmp[s];
					//printf("[opti: message damping]msg = %Lf\n", msg_tmp[s]);
					msg_sum += msg_tmp[s];

					//test
					//if(t==1){
					//	printf("test1: %d->%d, msg[s%d]:%.10Lf\n", i, ednode->headvex, s, msg_tmp[s]);
					//}
				}

				//normalize the message
				//printf("msg_sum=%.10Lf\n", msg_sum);
				//k = 1 / msg_sum;
				for(s=0; s<NUM_STATES; s++){
					ednode->msg_prior[s] = ednode->msg[s];
					//ednode->msg[s] = k * msg_tmp[s];
					ednode->msg[s] = msg_tmp[s] / msg_sum;

					//if message is changed, it's not converged
					//if((ednode->msg[s] != ednode->msg_prior[s]) && fabs(ednode->msg[s] - ednode->msg_prior[s]) > MSG_MINI_THRESHOLD){
					//	flag = 1;
					//}
					if(flag == 0 && fabs(ednode->msg[s] - ednode->msg_prior[s]) > MSG_MINI_THRESHOLD){
						flag = 1;
					}

					//here is only for test
					//if (fabs(ednode->msg[s] - ednode->msg_prior[s]) <= MSG_MINI_THRESHOLD){
					//	printf("t=%d: test fabs: %.12f\n", t, fabs(ednode->msg[s] - ednode->msg_prior[s]));
					//}

					//test
					//printf("%d->%d, msg[s%d]:(%.20Lf)\n", i, ednode->headvex, s, ednode->msg[s]);
				}
				ednode->iter = t;

				//move to next edge
				ednode = ednode->outlink;
			}
		}
		#ifdef DEBUG_TIMER_EACH_ITER
		end = clock();
		printf("%d iteration time: %f\n", t, (double)(end-start)/CLOCKS_PER_SEC);
		#endif

		//pruning
		if(flag == 0){
			//test
			printf("message converge!\n");
			#ifdef DEBUG
			//print_node_message();
			#endif
			break;
		}

		//test
		//print_node_message();
	}

	//update all the belief
	printf("updating the node belief ...\n");
	for(i=0; i<NUM_NODES; i++) {
		long double belief_sum = 0.0;

		for(s=0; s<NUM_STATES; s++){
			long double belief = AdjList[i].belief[s];

			//multiple the message from its neighbers
			ednode = AdjList[i].first_in;
			while(ednode){
				belief *= ednode->msg[s];
				ednode = ednode->inlink;
			}
			//printf("2:node %d: belief=%.20Lf\n", i, belief);
			AdjList[i].belief[s] = belief;

			belief_sum += belief;
		}
		//printf("belief_sum=%.20Lf\n", belief_sum);

		//normalize the belief
		k = 1 / belief_sum;
		for(s=0; s<NUM_STATES; s++){
			AdjList[i].belief[s] *= k;
		}
	}
	//printf("\n");
	//print_node_belief();
	print_node_belief_write_file(outputfile);
}


int init_graph(){
	int i, s;

	AdjList = NULL;
	AdjList = (struct vertexNode*) malloc(NUM_NODES * sizeof(struct vertexNode));  
	if(AdjList == NULL){
		printf("memery allocation err: AdjList[]\n");
		return -1;
	}
	#ifdef DEBUG
	printf("[debug]memory allocation done: AdjList[] (%d x sizeof(struct vertexNode))\n", NUM_NODES);
	#endif

	for(i=0; i<NUM_NODES; i++){
		//printf("%d ", i);
		AdjList[i].belief = (long double*) malloc(NUM_STATES * sizeof(long double));
		AdjList[i].degree = 0;
		AdjList[i].msg_fact = 0;
		if(AdjList[i].belief == NULL){
			printf("memery allocation err: AdjList[%d].belief\n", i);
			return -1;
		}

		for(s=0; s<NUM_STATES; s++){
			AdjList[i].belief[s] = 0.0;
		}

		AdjList[i].first_in = NULL;
		AdjList[i].first_out = NULL;
	}
	#ifdef DEBUG
	printf("[debug]memory allocation done: AdjList[i].belief[] (%d x %d x sizeof(long double))\n", NUM_NODES, NUM_STATES);
	#endif

	label = NULL;
	label = (int *) malloc(NUM_NODES * sizeof(int));
	if(label == NULL){
		printf("memery allocation err: label\n");
		return -1;
	}
	#ifdef DEBUG
	printf("[debug]memory allocation done: label[] (%d x sizeof(int))\n", NUM_NODES);
	#endif

	#ifdef DEBUG
	printf("[debug]sizeof(int)=%d, sizeof(float)=%d, sizeof(double)=%d, sizeof(long double)=%d\n", 
		(int)sizeof(int), (int)sizeof(float), (int)sizeof(double), (int)sizeof(long double));
	printf("[debug]sizeof(struct vertexNode)=%d, sizeof(struct edgeNode)=%d\n\n", (int)sizeof(struct vertexNode), (int)sizeof(struct edgeNode));
	#endif 


	return 0;
}


struct edgeNode* get_edgenode(int tailvex, int headvex){
	int s;
	struct edgeNode *edge_node = NULL;

	edge_node = (struct edgeNode*)malloc(sizeof(struct edgeNode));
	if(edge_node == NULL){
		printf("memery allocation err: get_edgenode(): edge_node\n");
		return NULL;
	}

	edge_node->msg = (long double*) malloc(NUM_STATES * sizeof(long double));
	if(edge_node->msg == NULL){
		printf("memery allocation err: edge_node.msg\n");
		return NULL;
	}

	edge_node->msg_prior = (long double*) malloc(NUM_STATES * sizeof(long double));
	if(edge_node->msg_prior == NULL){
		printf("memery allocation err: edge_node.msg_prior\n");
		return NULL;
	}

	edge_node->tailvex = tailvex;
	edge_node->headvex = headvex;
	edge_node->iter = 0;
	edge_node->inlink = NULL;
	edge_node->outlink = NULL;
	for(s=0; s<NUM_STATES; s++){
		edge_node->msg[s] = edge_node->msg_prior[s] = 0.0;
	}

	return edge_node;
}


void destroy_graph(){
	//TODO
	int i,j;
	struct edgeNode *tmp1 = NULL;
	struct edgeNode *tmp2 = NULL;

	for(i=0; i<NUM_NODES; i++){
		if(AdjList[i].belief != NULL){
			free(AdjList[i].belief);
		}
	}
	for(i=0; i<NUM_NODES; i++){
		tmp1 = AdjList[i].first_out;
		while(tmp1){
			tmp2 = tmp1;
			tmp1 = tmp1->outlink;
			free(tmp2);
		}
	}
	if(AdjList != NULL){
		free(AdjList);
	}

	if(label != NULL){
		free(label);
	}

	for(i=0; i<NUM_STATES; i++){
		if(edge_potential[i]){
			free(edge_potential[i]);
		}
	}
	if(edge_potential != NULL){
		free(edge_potential);
	}
}

void print_graph(){
	int i, j;
	struct edgeNode *ednode = NULL;

	printf("Graph:\n");
	for(i=0; i<NUM_NODES; i++){
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		printf("[out]%d: ", i);
		ednode = AdjList[i].first_out;
		while(ednode){
			printf("(%d->%d) ", ednode->tailvex, ednode->headvex);
			ednode = ednode->outlink;
		}
		printf("Degree: %d\n", AdjList[i].degree);

		printf("[in ]%d: ", i);
		ednode = AdjList[i].first_in;
		while(ednode){
			printf("(%d->%d) ", ednode->tailvex, ednode->headvex);
			ednode = ednode->inlink;
		}
		printf("\n");
	}
}

//output:
// max_degree, min_degree, avg_degree
//output:
// max_degree, min_degree, avg_degree
void print_degree(){
	int i;
	struct edgeNode *ednode = NULL;
	int degree_cnt = 0;
	int degree_sum = 0;
	int degree_max = 0;
	int degree_min = 0;
	float degree_avg = 0.0;
	int flag = 0;

 	printf("Graph Degree:\n");
	for(i=0; i<NUM_NODES; i++){
		degree_cnt = 0;
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		//printf("%d: ", i);
		ednode = AdjList[i].first_out;
		while(ednode){
			degree_cnt++;
			ednode = ednode->outlink;
		}
		//printf("%d\n", degree_cnt);
		AdjList[i].degree = degree_cnt;
		AdjList[i].msg_fact = degree_cnt/(int)MAX_LEN;

		//calculate sum, avg, max, min
		degree_sum +=  degree_cnt;
		if(flag == 0){
			degree_max = degree_cnt;
			degree_min = degree_cnt;
			flag = 1;
		}
		else{
			if(degree_cnt > degree_max){
				degree_max = degree_cnt;
			}
			else if(degree_cnt < degree_min){
				degree_min = degree_cnt;
			}
		}
	}

	degree_avg = (float)degree_sum / (float)NUM_NODES;
	//printf("The average degree: %.2f\n", degree_avg);

	printf("--------------\nmax_degree: %d\nmin_degree: %d\navg_degree: %.2f\n--------------\n",
		degree_max, degree_min, degree_avg);
}

void print_degree_and_write_file(char *filepath){
	int i;
	struct edgeNode *ednode = NULL;
	int openfile_flag;
	char buf[1024];
	int fd;
	int degree_cnt = 0;
	int degree_sum = 0;
	int degree_max = 0;
	int degree_min = 0;
	float degree_avg = 0.0;
	int flag = 0;

        openfile_flag = O_CREAT|O_RDWR|O_TRUNC;	//Overwrite mode
	if((fd=open(filepath, openfile_flag, 0644)) < 0){
		printf("open %s failed \n", filepath);
		return;
	}

	printf("Graph Degree:\n");
	for(i=0; i<NUM_NODES; i++){
		degree_cnt = 0;
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		//printf("%d: ", i);
		ednode = AdjList[i].first_out;
		while(ednode){
			degree_cnt++;
			ednode = ednode->outlink;
		}
		//printf("%d\n", degree_cnt);
		AdjList[i].degree = degree_cnt;
		AdjList[i].msg_fact = degree_cnt/(int)MAX_LEN;

		//calculate sum, avg, max, min
		degree_sum +=  degree_cnt;
		if(flag == 0){
			degree_max = degree_cnt;
			degree_min = degree_cnt;
			flag = 1;
		}
		else{
			if(degree_cnt > degree_max){
				degree_max = degree_cnt;
			}
			else if(degree_cnt < degree_min){
				degree_min = degree_cnt;
			}
		}


		sprintf(buf, "%d: %d, %d\n", i, degree_cnt, AdjList[i].msg_fact);
		#ifdef DEBUG
		printf("%s", buf);
		#endif
		if(write(fd,buf,strlen(buf)) < 0){
			printf("write file failed!\n");
			return;
		}
	}

	degree_avg = (float)degree_sum / (float)NUM_NODES;
	//printf("The average degree: %.2f\n", degree_avg);


	sprintf(buf, "--------------\nmax_degree: %d\nmin_degree: %d\navg_degree: %.2f\n--------------\n",
		degree_max, degree_min, degree_avg);
	//if(write(fd,buf,strlen(buf)) < 0){
	//	printf("write file failed!\n");
	//	return;
	//}
	printf("%s", buf);
	close(fd);
}

void print_node_belief(){
	int i, s;

	for(i=0; i<NUM_NODES; i++){
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		printf("%d: [%.20Lf", i, AdjList[i].belief[0]);
		for(s=1; s<NUM_STATES; s++){
			printf(", %.20Lf", AdjList[i].belief[s]);
		}
		printf("]\n");
	}
}

/* print the belief result on the screen and save it into a file */
void print_node_belief_write_file(char *filepath){
	int i, s;
	int fd;
	int openfile_flag;
	//char buf[5120];
	char buf[BUF_MAX_LEN];
	int flag;
	int belief_len;

	printf("write the belief value into a file ...\n");
        //openfile_flag = O_CREAT|O_RDWR|O_APPEND;	//Append mode
        openfile_flag = O_CREAT|O_RDWR|O_TRUNC;	//Overwrite mode
	if((fd=open(filepath, openfile_flag, 0644)) < 0){
		printf("open %s failed \n", filepath);
		return;
	}

	flag = 0;
	belief_len = 0;
	for(i=0; i<NUM_NODES; i++){
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		sprintf(buf+strlen(buf), "%d: [%.20Lf", i, AdjList[i].belief[0]);
		for(s=1; s<NUM_STATES; s++){
			sprintf(buf+strlen(buf), ", %.20Lf", AdjList[i].belief[s]);
		}
		sprintf(buf+strlen(buf), "]\n");

		if(flag == 0){
			belief_len = (int)strlen(buf);
			flag = 1;
		}

		#ifdef DEBUG
		printf("%s", buf);
		printf("%d\n", (int)strlen(buf));
		#endif

		//if((int)strlen(buf) > 4096){
		if((int)strlen(buf) > (BUF_MAX_LEN - belief_len)){
			if(write(fd,buf,strlen(buf)) < 0){
				printf("write file failed!\n");
				return;
			}
			buf[0]='\0';
			//printf("test: %d\n", (int)strlen(buf));
		}
	}
	if((int)strlen(buf) > 0){
		if(write(fd,buf,strlen(buf)) < 0){
			printf("write file failed!\n");
			return;
		}
	}

	close(fd);
	printf("saved into file: %s\n", filepath);
}


void print_node_message(){
	int i,s;
	struct edgeNode *ednode = NULL;

	for(i=0; i<NUM_NODES; i++){
		//pruning
		//if(label[i]>0){
		//	continue;
		//}

		ednode = AdjList[i].first_out;
		while(ednode){
		//printf("%d: [%.20Lf", i, ednode.msg[0]);
			printf("(iter=%d) m(%d,%d): [%.20Lf", ednode->iter, i, ednode->headvex, ednode->msg[0]);
			for(s=1; s<NUM_STATES; s++){
				printf(", %.20Lf", ednode->msg[s]);
			}
			printf("]\n");
			ednode = ednode->outlink;
		}
	}
}


/* 
 * Read the graph and the initial belief value 
 * Set the nodes[NUM_NODES].belief[NUM_STATES], G[NUM_NODES][NUM_NODES]
 */
int read_graph(char* graph_nodes_file, char* graph_edges_file) {
     	FILE *fp; 
     	char line[1024];
	char *tok, *buf;
	int flag, node, node_neig, state;
	int i, j, s;
	struct edgeNode *ednode = NULL;
	struct edgeNode *tmp = NULL;
	int max_node_num;
	int max_state;
	double init_msg_value;
	int test_i=0;

	printf("[debug]read_graph from file\n");
	if(graph_nodes_file == NULL || graph_edges_file == NULL){
		printf("no data file found!\n");
		return -1;
	}

	//init_graph(); //initial MAX_NUM_NODES nodes

	printf("reading the graph nodes ...\n");
	//read the nodes initial belief value
     	if((fp = fopen(graph_nodes_file,"r")) == NULL) { 
         	printf("read file %s error!\n", graph_nodes_file); 
         	return -1; 
     	} 

	max_node_num = 0;
	max_state = 0;
     	while (1) { 
         	fgets(line, 1024, fp);         	
		if (feof(fp)){
			break;
		}
		//printf("%s\n", line);

		buf = (char*)line;
		tok = strsep(&buf, " ");
		flag = 1;
		while(tok){
			//printf("test: %s\n", tok);
			if(flag == 1){
				//get the node number
				node = atoi(tok);
				if(node > max_node_num){
					max_node_num = node;
				}
			}
			else if(flag == 2){
				if((char)*tok != 's'){
					printf("input file %s error!(state format error)\n", graph_nodes_file);
					return -1;
				}

				tok = tok+1;
				state = atoi(tok);
				if(state > max_state){
					max_state = state;
				}			
			}
			else{
				AdjList[node].belief[state-1] = atof(tok);
			}

			flag++;
			tok = strsep(&buf, " ");
		}	
     	}
     	fclose(fp);
	//print_graph();
	//print_node_belief();

	//need the node number to begin with 0 in the input file
	//NUM_NODES = max_node_num + 1;
	//printf("[test]NUM_NODES = %d; count from input: %d\n", NUM_NODES, max_node_num + 1);
	//need the state number to begin with 0 in the input file
	//NUM_STATES = max_state;
	//printf("[test]NUM_STATES = %d; count from input: %d\n", NUM_STATES, max_state);

	printf("reading the graph edges ...\n");
	//read the edges (undirected garph)
	if((fp = fopen(graph_edges_file,"r")) == NULL) { 
         	printf("read file %s error!\n", graph_edges_file); 
         	return -1; 
     	} 

	init_msg_value = (long double)1/(long double)NUM_STATES;
     	while (1) { 
         	fgets(line, 1024, fp);         	
		if (feof(fp)){
			break;
		}
		//printf("%s\n", line);

		buf = (char*)line;
		tok = strsep(&buf, " ");
		flag = 1;
		while(tok){
			//printf("test: %s\n", tok);
			if(flag == 1){
				//get the node1 number
				i = atoi(tok);
			}
			else if(flag == 2){
				//get the node2 number
				j = atoi(tok);

				//create two edge node (for undirected graph)
				ednode = get_edgenode(i, j);
				ednode->iter = 0;
				for(s=0; s<NUM_STATES; s++){
					ednode->msg[s] = ednode->msg_prior[s] = init_msg_value;
				}
				//add this node to the edge list (insert at the beginning)
				tmp = AdjList[i].first_out;
				AdjList[i].first_out = ednode;
				ednode->outlink = tmp;
				//inverse adjacency list
				tmp = AdjList[j].first_in;
				AdjList[j].first_in = ednode;
				ednode->inlink = tmp;


				//another edge node
				ednode = get_edgenode(j, i);
				ednode->iter = 0;
				for(s=0; s<NUM_STATES; s++){
					ednode->msg[s] = ednode->msg_prior[s] = init_msg_value;
				}
				//add this node to the edge list (insert at the beginning)
				tmp = AdjList[j].first_out;
				AdjList[j].first_out = ednode;
				ednode->outlink = tmp;
				//inverse adjacency list
				tmp = AdjList[i].first_in;
				AdjList[i].first_in = ednode;
				ednode->inlink = tmp;			 
			}
			//Reserved for edge weight(not used now)
			else{		
				//Reserve for weighted graph
				printf("Error in input graph file\n");
				return -1;
			}

			flag++;
			tok = strsep(&buf, " ");
		}	
     	}
	fclose(fp);

	printf("read_graph finish\n");
	//print_graph();
	//print_node_belief();
	return 0;
}

/* the size of the edge potential should be same with the size of "enum STATES"*/
int init_edge_potential(){
	int i,j;

	printf("[debug]in init_edge_potential()\n");
	edge_potential = NULL;
	edge_potential = (float**) malloc(NUM_STATES * sizeof(float*));
	if(edge_potential == NULL){
		printf("memery allocation err: edge_potential\n");
		return -1;
	}

	for(i=0; i<NUM_STATES; i++){
		edge_potential[i] = (float *)malloc(NUM_STATES * sizeof(float));
		for(j=0; j<NUM_STATES; j++){
			edge_potential[i][j] = -1.0;
		}
	}
}

void print_edge_potential(){
	int i,j;
	for(i=0; i<NUM_STATES; i++){
		for(j=0; j<NUM_STATES; j++){
			printf("%f, ", edge_potential[i][j]);
		}
		printf("\n");
	}
}

int read_edge_potential(char* ep_file){
     	FILE *fp; 
     	char line[1024];
	char *tok, *buf;
	int i, j;
	int flag;
	int max_state;
	int err;

	printf("[debug]read_edge_potential\n");
	if(ep_file == NULL){
		printf("no ep_file found!\n");
		return -1;
	}

	printf("[debug]init_edge_potential\n");
	err = init_edge_potential();
	if(err < 0){
		return -1;
	}
	//print_edge_potential();

     	if((fp = fopen(ep_file,"r")) == NULL) { 
         	printf("read ep_file %s error!\n", ep_file); 
         	return -1; 
     	} 
 
	i = 0;
	max_state = 0;
     	while (1) { 
         	fgets(line, 1024, fp);         	
		if (feof(fp)){
			break;
		}
		//printf("%s\n", line);
		
		buf = (char*)line;
		tok = strsep(&buf, " ");
		flag = 0;
		while(tok){
			//test
			//printf("test_ep_file: %s\n", tok);
			if(flag == 0){
				if((char)*tok != 's'){
					printf("input file %s error!(state format error)\n", ep_file);
					return -1;
				}

				tok = tok+1;
				i = atoi(tok);
				if(i > max_state){
					max_state = i;
				}			
			}
			else if(flag == 1){
				if((char)*tok != 's'){
					printf("input file %s error!(state format error)\n", ep_file);
					return -1;
				}

				tok = tok+1;
				j = atoi(tok);
			}
			else{
				edge_potential[i-1][j-1] = atof(tok);
			}

			tok = strsep(&buf, " ");
			flag++;
		}
	}

	//ensure the NUM_STATES is right
	if(NUM_STATES != (max_state)){
		printf("warning! NUM_STATES is error!\n");
		//return -1;
	}

	//test
	//print_edge_potential();

	printf("[debug]read_edge_potential finished.\n");
	return 0;
}


/* Purning the graph 
 * traver the graph and label its connected components consist of one node or only unknown nodesss
 *
 */
/*
int pruning_graph(){
	int i, j, s;
	int *a;  //queue for traveling
	int f,r;
	int v;
	int flag_one_node, flag_all_unknown_nodes;
	long double unknown_belief;

	a = (int*) malloc(NUM_NODES * sizeof(int));
	if(a == NULL){
		printf("memery allocation err: a\n");
		return -1;
	}

	unknown_belief = (long double)1/(long double)NUM_STATES;
	//printf("unknown_belief: %f\n", unknown_belief);
	for(i=0; i<NUM_NODES; i++){
		if(label[i] == -1){
			//printf("loop_node = %d\n", i);
			//bfs(p,i,label);

			f = r = 0;
			a[r] = i;
			r++;
			flag_one_node = 0;
			flag_all_unknown_nodes = 0;
			while(f!=r){
				v = a[f];
				f++;
				//label[v]++;
				label[v]=0;

				//printf("loop_node: f=%d, r=%d, v=%d\n", f, r, v);

				//1/NUM_STATES; //for 2 states, it's 0.5; 4 states, it's 0.25
				//if(nodes[v].belief != 0.5){  //it's an unknow node
				for(s=0; s<NUM_STATES; s++){
					//printf("nodes[v].belief[s]:%f, flag_all_unknown_nodes=%d\n", nodes[v].belief[s], flag_all_unknown_nodes);
					//TODO doesn't work for 4 states! Because it depends on how to define the initial belief value! for (0,0,0.5,0.5), it doesn't work!
					if(nodes[v].belief[s] != unknown_belief){  //it's an unknown node
						flag_all_unknown_nodes = 1;
					}
				}

				for(j=0; j<NUM_NODES; j++){
					if(G[v][j] >= 0.0 && label[j] == -1){ //there is an edge
						a[r] = j;
						r++;

						flag_one_node = 1;
					}
				}
			}
			//printf("flag_all_unknown_nodes=%d\n", flag_all_unknown_nodes);
			//print_pruning_flag();
			//use j as the one node component flag 
			if(flag_one_node == 0){ // this connected component has only one node
				//label[i]++; //lable[i]=1; i has no neighbors, it's a single node connected component, so cut this node
				label[i]=1;
			}
			//print_pruning_flag();
			else if(flag_all_unknown_nodes == 0){ //all the nodes in this connected component have an unknown state
				for(j=0; j<r; j++){
					//label[a[j]]++;
					label[a[j]]=1;
				}
			}
			//print_pruning_flag();

		}		
	}
	return 0;
}

void print_pruning_flag(){
	int i;

	printf("Labels: ");
	for(i=0; i<NUM_NODES; i++){
		printf("%d:[%d] ", i, label[i]);
	}
	printf("\n");
}
*/

void usage(char *cmd){
	//printf("Usage: %s <graph_initial_states_file> <graph_edges_file> <bp_edge_potential_file>\n", cmd);
	printf("Usage: %s <graph_initial_states_file> <graph_edges_file> <bp_edge_potential_file> <number_of_nodes> <number_of_states>\n", cmd);
}


int main(int argc, char* argv[])
{
	char *graph_nodes_file = NULL;
	char *graph_edges_file = NULL;
	char *ep_file = NULL;
	int err;
	clock_t start, end;

	if(argc < 6){
		usage(argv[0]);
		return -1;
	}

	graph_nodes_file = argv[1];
	graph_edges_file = argv[2];
	ep_file = argv[3];
	NUM_NODES = atoi(argv[4]);
	NUM_STATES = atoi(argv[5]);

	if(argc >= 7){
		BP_ITER = atoi(argv[6]);
	}

	start = clock();
	err = init_graph();
	if(err<0){
		return -1;
	}

	err = read_graph(graph_nodes_file, graph_edges_file);
	if(err < 0){
		return -1;
	}

	err = read_edge_potential(ep_file);
	if(err < 0){
		return -1;
	}
	end = clock();
	printf("Construting the graph, time=%f\n", (double)(end-start)/CLOCKS_PER_SEC);

	//test the graph here
	//print_initial_value();

	//comput the degree
	start = clock();
	//print_degree_and_write_file(outputdegree);
	print_degree();
	end = clock();
	printf("Count the degree, time=%f\n", (double)(end-start)/CLOCKS_PER_SEC);

	//test
	#ifdef DEBUG
	print_initial_value();
	#endif

	//pruning the graph
	//pruning_graph();
	#ifdef DEBUG
	//print_pruning_flag();
	#endif

	//belief propagation
	printf("running the belief propagation algorithm.\n");
	start = clock();
	bp_alg();
	end = clock();
	printf("BP running time=%f\n", (double)(end-start)/CLOCKS_PER_SEC);

	//start = clock();
	destroy_graph();
	//end = clock();
	//printf("Destroy the graph, time=%f\n", (double)(end-start)/CLOCKS_PER_SEC);

	return 0;
}


void print_initial_value(){
	printf("-----Initial information-----\n");
	print_graph();
	printf("print degree info.:\n");
	print_degree();
	printf("print initial node belief:\n");
	print_node_belief();
	printf("print initial message:\n");
	print_node_message();
	printf("print edge potential:\n");
	print_edge_potential();
	printf("-----------------------------\n");
}



