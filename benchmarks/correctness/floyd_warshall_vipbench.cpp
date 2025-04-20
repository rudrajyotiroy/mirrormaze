// C Program for Floyd Warshall Algorithm
#include <stdio.h>
#include <stdint.h>
#include <limits.h>
#include <stdlib.h>
#include <time.h>
 
// Number of vertices in the graph
#define V 30
#define ITER 100
 
/* Define Infinite as a large enough value. This value will be used
  for vertices not connected to each other */
#define INF 99999
#define N 99999

// A function to print the solution matrix
void printSolution(int dist[][V]);


/* Fisher–Yates shuffle */
static void shuffle(int *array, int n) {
    for (int i = n - 1; i > 0; --i) {
        int j = rand() % (i + 1);
        int tmp = array[i];
        array[i] = array[j];
        array[j] = tmp;
    }
}

/* Generate a connected undirected graph on num_vertices vertices.
 * extra_p = probability [0.0–1.0] of adding each extra edge */
int **generate_graph(int num_vertices, double extra_p) {
    /* cast malloc for C++ */
    int **g = (int **)malloc(num_vertices * sizeof(int *));
    if (!g) { perror("malloc"); exit(EXIT_FAILURE); }

    for (int i = 0; i < num_vertices; ++i) {
        g[i] = (int *)malloc(num_vertices * sizeof(int));
        if (!g[i]) { perror("malloc"); exit(EXIT_FAILURE); }
        for (int j = 0; j < num_vertices; ++j)
            g[i][j] = (i == j ? 0 : N);
    }

    /* 1) Build a random spanning tree */
    int *order = (int *)malloc(num_vertices * sizeof(int));
    if (!order) { perror("malloc"); exit(EXIT_FAILURE); }
    for (int i = 0; i < num_vertices; ++i) order[i] = i;
    shuffle(order, num_vertices);
    for (int i = 1; i < num_vertices; ++i) {
        int u = order[i - 1], v = order[i];
        int w = rand() % 100 + 1;  /* weight in [1..100] */
        g[u][v] = g[v][u] = w;
    }
    free(order);

    /* 2) Add extra random edges */
    for (int i = 0; i < num_vertices; ++i) {
        for (int j = i + 1; j < num_vertices; ++j) {
            if (g[i][j] == N && (rand() / (double)RAND_MAX) < extra_p) {
                int w = rand() % 100 + 1;
                g[i][j] = g[j][i] = w;
            }
        }
    }

    return g;
}

// Solves the all-pairs shortest path problem using Floyd Warshall algorithm
void
floydWarshall (int** graph __attribute((annotate("secret"))), int dist[][V])
{
  /* dist[][] will be the output matrix that will finally have the shortest 
    distances between every pair of vertices */
  int i, j, k;
 
  /* Initialize the solution matrix same as input graph matrix. Or 
     we can say the initial values of shortest distances are based
     on shortest paths considering no intermediate vertex. */
  for (i = 0; i < V; i++)
    for (j = 0; j < V; j++)
      dist[i][j] = graph[i][j];
 
  /* Add all vertices one by one to the set of intermediate vertices.
    ---> Before start of a iteration, we have shortest distances between all
    pairs of vertices such that the shortest distances consider only the
    vertices in set {0, 1, 2, .. k-1} as intermediate vertices.
    ----> After the end of a iteration, vertex no. k is added to the set of
    intermediate vertices and the set becomes {0, 1, 2, .. k} */
  for (k = 0; k < V; k++)
  {
    // Pick all vertices as source one by one
    for (i = 0; i < V; i++)
    {
      // Pick all vertices as destination for the
      // above picked source
      for (j = 0; j < V; j++)
      {
        // If vertex k is on the shortest path from
        // i to j, then update the value of dist[i][j]
#ifdef VIP_DO_MODE
        VIP_ENCBOOL _pred = (dist[i][k] + dist[k][j] < dist[i][j]);
        dist[i][j] = VIP_CMOV(_pred, dist[i][k] + dist[k][j], dist[i][j]);
#else /* !VIP_DO_MODE */
        if (dist[i][k] + dist[k][j] < dist[i][j])
          dist[i][j] = dist[i][k] + dist[k][j];
#endif /* VIP_DO_MODE */
      }
    }
  }
}
 
/* A utility function to print solution */
void
printSolution(int dist[][V])
{
    printf ("Following matrix shows the shortest distances"
            " between every pair of vertices \n");
    for (int i = 0; i < V; i++)
    {
        for (int j = 0; j < V; j++)
        {
            if (dist[i][j] == INF)
                printf("%7s", "INF");
            else
                printf ("%7d", dist[i][j]);
        }
        printf("\n");
    }
}
 
// driver program to test above function
int
main(void)
{
  /* Let us create the following weighted graph
          10
     (0)------->(3)
      |         /|\
    5 |          |
      |          | 1
     \|/         |
     (1)------->(2)
          3           */
#ifdef notdef
  int graph[V][V] = { {0,   5,  INF, 10},
                      {INF, 0,   3, INF},
                      {INF, INF, 0,   1},
                      {INF, INF, INF, 0}
                    };
#endif /* notdef */
// 	int graph[V][V] = {
//   // Vertex # A  B  C  D  E  F  G  H	   Vertex
//             { 0, N, 4, N, N, 7, N, N }, // A
// 			      { N, 0, N, N, 9, N, N, 3 }, // B
// 			      { 4, N, 0, 3, N, 2, 9, N }, // C	
// 			      { N, N, 3, 0, 3, N, 7, N }, // D
// 			      { N, 9, N, 3, 0, N, 2, 7 }, // E
// 			      { 7, N, 2, N, N, 0, 8, N }, // F
// 			      { N, N, 9, 7, 2, 8, 0, 3 }, // G
// 			      { N, 3, N, N, 7, N, 3, 0 } };//H

    // distance array
    int dist[V][V];
    srand((unsigned)time(NULL));

    double extraEdgeP = 0.5;     /* probability for extra edges */
    for (int i = 0; i < ITER; i++){
        int **graph = generate_graph(V, extraEdgeP);
        floydWarshall(graph, dist);
    }

    // Print the shortest distance matrix
    printSolution(dist);
    return 0;
}
