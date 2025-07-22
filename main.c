#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
#include <math.h>

// ============================================================================
// 1. DATA STRUCTURES & FORWARD DECLARATIONS
// ============================================================================

#define MAX_AIR_ROUTES 5

// A structure to represent a unidirectional air route.
typedef struct {
    uint16_t dest_x;
    uint16_t dest_y;
    uint8_t cost;
} AirRoute;

// A structure representing a single hexagon tile on the map.
typedef struct {
    uint8_t cost;
    uint8_t num_air_routes;
    AirRoute air_routes[MAX_AIR_ROUTES];
} Hexagon;

// Node for the priority queue used in A*.
typedef struct {
    int64_t priority;
    uint16_t x;
    uint16_t y;
} PQNode;

// The priority queue structure itself.
typedef struct {
    PQNode *nodes;
    size_t size;
    size_t capacity;
} PriorityQueue;

// A single entry in the cache.
typedef struct CacheEntry {
    uint16_t source_x;
    uint16_t source_y;
    int64_t* distances;
    struct CacheEntry *prev;
    struct CacheEntry *next;
    struct CacheEntry *h_next;
} CacheEntry;

// --- Global state ---
Hexagon** map = NULL;
uint32_t map_cols = 0;
uint32_t map_rows = 0;

// --- Function Forward Declarations ---
void cleanup_resources();

// ============================================================================
// 2. PRIORITY QUEUE (BINARY MIN-HEAP) IMPLEMENTATION
// ============================================================================

static void sift_up(PriorityQueue* pq, size_t index) {
    size_t parent_idx = (index - 1) / 2;
    PQNode temp = pq->nodes[index];
    while (index > 0 && pq->nodes[parent_idx].priority > temp.priority) {
        pq->nodes[index] = pq->nodes[parent_idx];
        index = parent_idx;
        parent_idx = (index - 1) / 2;
    }
    pq->nodes[index] = temp;
}

static void sift_down(PriorityQueue* pq, size_t index) {
    size_t left_child_idx;
    size_t min_child_idx;
    PQNode temp = pq->nodes[index];

    while ((left_child_idx = 2 * index + 1) < pq->size) {
        min_child_idx = left_child_idx;
        size_t right_child_idx = left_child_idx + 1;
        if (right_child_idx < pq->size && pq->nodes[right_child_idx].priority < pq->nodes[left_child_idx].priority) {
            min_child_idx = right_child_idx;
        }

        if (temp.priority <= pq->nodes[min_child_idx].priority) {
            break;
        }

        pq->nodes[index] = pq->nodes[min_child_idx];
        index = min_child_idx;
    }
    pq->nodes[index] = temp;
}

static PriorityQueue* pq_create(size_t initial_capacity) {
    PriorityQueue* pq = (PriorityQueue*)malloc(sizeof(PriorityQueue));
    pq->nodes = (PQNode*)malloc(initial_capacity * sizeof(PQNode));
    pq->size = 0;
    pq->capacity = initial_capacity;
    return pq;
}

static void pq_destroy(PriorityQueue* pq) {
    if (pq) {
        free(pq->nodes);
        free(pq);
    }
}

static void pq_push(PriorityQueue* pq, PQNode node) {
    if (pq->size == pq->capacity) {
        pq->capacity *= 2;
        pq->nodes = (PQNode*)realloc(pq->nodes, pq->capacity * sizeof(PQNode));
    }
    pq->nodes[pq->size] = node;
    pq->size++;
    sift_up(pq, pq->size - 1);
}

static PQNode pq_pop(PriorityQueue* pq) {
    PQNode top = pq->nodes[0];
    pq->nodes[0] = pq->nodes[pq->size - 1];
    pq->size--;
    if (pq->size > 0) {
        sift_down(pq, 0);
    }
    return top;
}

static bool pq_is_empty(const PriorityQueue* pq) {
    return pq->size == 0;
}

// ============================================================================
// 3. LRU CACHE IMPLEMENTATION
// ============================================================================

static CacheEntry** hash_table = NULL;
static CacheEntry* head = NULL;
static CacheEntry* tail = NULL;
static size_t cache_size = 0;
static size_t cache_capacity = 0;
static size_t hash_table_size = 0;

static unsigned int hash(uint16_t x, uint16_t y) {
    return (x * 31 + y) % hash_table_size;
}

static void destroy_cache(); // Forward declare for init_cache

static void init_cache(size_t capacity) {
    if (hash_table) {
        destroy_cache();
    }
    cache_capacity = capacity;
    if (capacity == 0) return;

    hash_table_size = capacity * 2;
    hash_table = (CacheEntry**)calloc(hash_table_size, sizeof(CacheEntry*));
    head = NULL;
    tail = NULL;
    cache_size = 0;
}

static void destroy_cache() {
    if (!hash_table) return;
    CacheEntry* current = head;
    while (current) {
        CacheEntry* next = current->next;
        free(current->distances);
        free(current);
        current = next;
    }
    free(hash_table);
    hash_table = NULL;
    head = tail = NULL;
    cache_size = 0;
}

static void invalidate_cache() {
    destroy_cache();
    init_cache(cache_capacity);
}

static void detach_node(CacheEntry* entry) {
    if (entry->prev) entry->prev->next = entry->next;
    else head = entry->next;
    if (entry->next) entry->next->prev = entry->prev;
    else tail = entry->prev;
}

static void attach_to_head(CacheEntry* entry) {
    entry->next = head;
    entry->prev = NULL;
    if (head) head->prev = entry;
    head = entry;
    if (!tail) tail = head;
}

static int64_t* cache_get(uint16_t sx, uint16_t sy) {
    if (cache_capacity == 0) return NULL;
    unsigned int h = hash(sx, sy);
    CacheEntry* entry = hash_table[h];
    while (entry) {
        if (entry->source_x == sx && entry->source_y == sy) {
            detach_node(entry);
            attach_to_head(entry);
            return entry->distances;
        }
        entry = entry->h_next;
    }
    return NULL;
}

static void cache_put(uint16_t sx, uint16_t sy, int64_t* distances) {
    if (cache_capacity == 0) {
        free(distances);
        return;
    }
    if (cache_size >= cache_capacity) {
        CacheEntry* lru_entry = tail;
        detach_node(lru_entry);
        unsigned int h_lru = hash(lru_entry->source_x, lru_entry->source_y);
        CacheEntry* current = hash_table[h_lru];
        CacheEntry* prev = NULL;
        while(current) {
            if (current == lru_entry) {
                if (prev) prev->h_next = current->h_next;
                else hash_table[h_lru] = current->h_next;
                break;
            }
            prev = current;
            current = current->h_next;
        }
        free(lru_entry->distances);
        free(lru_entry);
        cache_size--;
    }
    CacheEntry* new_entry = (CacheEntry*)malloc(sizeof(CacheEntry));
    new_entry->source_x = sx;
    new_entry->source_y = sy;
    new_entry->distances = distances;
    attach_to_head(new_entry);
    unsigned int h = hash(sx, sy);
    new_entry->h_next = hash_table[h];
    hash_table[h] = new_entry;
    cache_size++;
}

// ============================================================================
// 4. MOVHEX CORE LOGIC AND COMMAND HANDLERS
// ============================================================================

static int64_t clamp(int64_t value, int64_t min, int64_t max) {
    if (value < min) return min;
    if (value > max) return max;
    return value;
}

static bool is_valid(uint16_t x, uint16_t y) {
    return x < map_cols && y < map_rows;
}

static void offset_to_cube(uint16_t col, uint16_t row, int* q, int* r, int* s) {
    // Formula corretta per la conversione da coordinate ODD-R a cubiche
    *q = col - (row - (row & 1)) / 2;
    *r = row;
    *s = -(*q) - (*r);
}

static int dist_esagoni(uint16_t x1, uint16_t y1, uint16_t x2, uint16_t y2) {
    int q1, r1, s1, q2, r2, s2;
    offset_to_cube(x1, y1, &q1, &r1, &s1);
    offset_to_cube(x2, y2, &q2, &r2, &s2);
    return (abs(q1 - q2) + abs(r1 - r2) + abs(s1 - s2)) / 2;
}

void do_init(uint32_t cols, uint32_t rows) {
    cleanup_resources();
    map_cols = cols;
    map_rows = rows;
    if (cols == 0 || rows == 0) {
        printf("OK\n");
        return;
    }
    map = (Hexagon**)malloc(cols * sizeof(Hexagon*));
    for (uint32_t i = 0; i < cols; ++i) {
        map[i] = (Hexagon*)malloc(rows * sizeof(Hexagon));
        for (uint32_t j = 0; j < rows; ++j) {
            map[i][j].cost = 1;
            map[i][j].num_air_routes = 0;
        }
    }
    init_cache(64); // Cache capacity can be tuned.
    printf("OK\n");
}

void do_change_cost(uint16_t x, uint16_t y, int v, int radius) {
    if (!is_valid(x, y) || radius <= 0 || ((v < -10) || (v > 10))) {
        printf("KO\n");
        return;
    }
    invalidate_cache();
    for (uint16_t xe = 0; xe < map_cols; ++xe) {
        for (uint16_t ye = 0; ye < map_rows; ++ye) {
            int dist = dist_esagoni(xe, ye, x, y);
            if (dist < radius) {
                double cost_change = floor((double)v * (double)(radius - dist) / (double)radius);
                int64_t new_cost = map[xe][ye].cost + (int64_t)floor(cost_change);
                map[xe][ye].cost = (uint8_t)clamp(new_cost, 0, 100);

                // if (cost_change != 0) {
                //     fprintf(stderr, "DEBUG: change_cost ha modificato (%u, %u). Vecchio costo: %lld, Nuovo costo: %u\n",
                //            xe, ye, (long long)map[xe][ye].cost - cost_change, map[xe][ye].cost);
                // }

                for (int i = 0; i < map[xe][ye].num_air_routes; ++i) {
                    int64_t new_air_cost = map[xe][ye].air_routes[i].cost + cost_change;
                    map[xe][ye].air_routes[i].cost = (uint8_t)clamp(new_air_cost, 0, 100);
                }
            }
        }
    }
    printf("OK\n");
}

void do_toggle_air_route(uint16_t x1, uint16_t y1, uint16_t x2, uint16_t y2) {
    if (!is_valid(x1, y1) || !is_valid(x2, y2)) {
        printf("KO\n");
        return;
    }
    invalidate_cache();
    Hexagon* source_hex = &map[x1][y1];
    int route_index = -1;
    for (int i = 0; i < source_hex->num_air_routes; ++i) {
        if (source_hex->air_routes[i].dest_x == x2 && source_hex->air_routes[i].dest_y == y2) {
            route_index = i;
            break;
        }
    }
    if (route_index != -1) {
        for (int i = route_index; i < source_hex->num_air_routes - 1; ++i) {
            source_hex->air_routes[i] = source_hex->air_routes[i + 1];
        }
        source_hex->num_air_routes--;
        printf("OK\n");
    } else {
        if (source_hex->num_air_routes >= MAX_AIR_ROUTES) {
            printf("KO\n");
            return;
        }
        double cost_sum = (double)source_hex->cost;
        for (int i = 0; i < source_hex->num_air_routes; ++i) {
            cost_sum += source_hex->air_routes[i].cost;
        }
        uint8_t new_cost = (uint8_t)floor(cost_sum / (source_hex->num_air_routes +1));
        source_hex->air_routes[source_hex->num_air_routes].dest_x = x2;
        source_hex->air_routes[source_hex->num_air_routes].dest_y = y2;
        source_hex->air_routes[source_hex->num_air_routes].cost = (uint8_t)clamp(new_cost, 0, 100);
        source_hex->num_air_routes++;
        printf("OK\n");
    }
}

// void do_travel_cost(uint16_t xp, uint16_t yp, uint16_t xd, uint16_t yd) {
//     if (!is_valid(xp, yp) || !is_valid(xd, yd)) {
//         //printf("DEBUG: Invalid coordinate ");
//         printf("-1\n");
//         return;
//     }
//     if (xp == xd && yp == yd) {
//         printf("0\n");
//         return;
//     }
//     int64_t* cached_distances = cache_get(xp, yp);
//     if (cached_distances) {
//         int64_t cost = cached_distances[xd * map_rows + yd];
//         //printf("DEBUG: Cached distance ");
//         printf("%ld\n", cost == LLONG_MAX ? -1 : cost);
//         return;
//     }
//
//     size_t map_size = map_cols * map_rows;
//     int64_t* distances = (int64_t*)malloc(map_size * sizeof(int64_t));
//     for (size_t i = 0; i < map_size; ++i) {
//         distances[i] = LLONG_MAX;
//     }
//     distances[xp * map_rows + yp] = 0;
//
//     PriorityQueue* pq = pq_create(128);
//     pq_push(pq, (PQNode){dist_esagoni(xp, yp, xd, yd), xp, yp});
//
//     while (!pq_is_empty(pq)) {
//         PQNode current = pq_pop(pq);
//         uint16_t ux = current.x, uy = current.y;
//         int64_t cost_so_far = distances[ux * map_rows + uy];
//
//         if (ux == xd && uy == yd) break;
//         //if (current.priority > cost_so_far + dist_esagoni(ux, uy, xd, yd)) continue;
//
//         Hexagon* u_hex = &map[ux][uy];
//         if (u_hex->cost > 0) {
//             // Vettori di direzione corretti e standard per una griglia "odd-r"
//             // La struttura è: [direzione][riga_pari_o_dispari][asse_x_o_y]
//             int directions[6][2][2] = {
//                 {{1,  0}, {1, -1}},  // Destra
//                 {{1,  1}, {1,  0}},  // Basso-Destra
//                 {{0,  1}, {0,  1}},  // Basso
//                 {{-1, 1}, {-1, 0}},  // Basso-Sinistra
//                 {{-1, 0}, {-1, -1}}, // Sinistra
//                 {{0, -1}, {0, -1}}   // Alto
//             };
//
//             for (int i = 0; i < 6; i++) {
//                 // Sceglie l'offset corretto in base alla parità della RIGA (uy)
//                 int offset_col = directions[i][uy % 2][0];
//                 int offset_row = directions[i][uy % 2][1];
//
//                 uint16_t vx = ux + offset_col;
//                 uint16_t vy = uy + offset_row;
//
//                 if (is_valid(vx, vy)) {
//                     int64_t new_cost = cost_so_far + u_hex->cost;
//                     if (new_cost < distances[vx * map_rows + vy]) {
//                         distances[vx * map_rows + vy] = new_cost;
//                         pq_push(pq, (PQNode){new_cost + dist_esagoni(vx, vy, xd, yd), vx, vy});
//                     }
//                 }
//             }
//
//             // Il ciclo delle rotte aeree deve essere DENTRO l'if (u_hex->cost > 0)
//             for (int i = 0; i < u_hex->num_air_routes; i++) {
//                 AirRoute* route = &u_hex->air_routes[i];
//                 if (route->cost > 0) { // Se vuoi ancora usare il costo della rotta come condizione
//                     // Il costo è la somma del costo di partenza e di quello di arrivo
//                     int64_t new_cost = cost_so_far + u_hex->cost;
//                     if (new_cost < distances[route->dest_x * map_rows + route->dest_y]) {
//                         distances[route->dest_x * map_rows + route->dest_y] = new_cost;
//                         pq_push(pq, (PQNode){new_cost + dist_esagoni(route->dest_x, route->dest_y, xd, yd), route->dest_x, route->dest_y});
//                     }
//                 }
//             }
//         }
//     }
//     pq_destroy(pq);
//
//     int64_t final_cost = distances[xd * map_rows + yd];
//     printf("%ld\n", final_cost == LLONG_MAX ? -1 : final_cost);
//     cache_put(xp, yp, distances);
// }

// Definisci una struttura per le coordinate, per rendere il codice più pulito
typedef struct {
    uint16_t x;
    uint16_t y;
} Point;

// Assicurati che le altre tue strutture (Hexagon, PQNode, etc.) e funzioni
// (dist_esagoni, pq_create, etc.) siano definite prima di questa funzione.

/*void do_travel_cost(uint16_t xp, uint16_t yp, uint16_t xd, uint16_t yd) {
    if (!is_valid(xp, yp) || !is_valid(xd, yd)) {
        printf("-1\n");
        return;
    }
    if (xp == xd && yp == yd) {
        printf("0\n");
        return;
    }

    int64_t* cached_distances = cache_get(xp, yp);
    if (cached_distances) {
        int64_t cost = cached_distances[xd * map_rows + yd];
        printf("%ld\n", cost == LLONG_MAX ? -1 : cost);
        return;
    }

    size_t map_size = map_cols * map_rows;
    int64_t* distances = (int64_t*)malloc(map_size * sizeof(int64_t));

    // ===== INIZIO MODIFICA: Aggiungi strutture per tracciare il percorso =====
    Point* parent = (Point*)malloc(map_size * sizeof(Point));
    char* move_type = (char*)calloc(map_size, sizeof(char)); // 'L' per Terra, 'A' per Aereo
    // ======================== FINE MODIFICA ========================

    for (size_t i = 0; i < map_size; ++i) {
        distances[i] = LLONG_MAX;
    }

    //Soluzione proposta per correggere il risultato-1 ottenuto in empty.txt
    // int costo_iniziale = map[yp][xp].cost;
    // distances[xp * map_rows + yp] = costo_iniziale;

    //Default
    distances[xp * map_rows + yp] = 0;

    PriorityQueue* pq = pq_create(128);
    pq_push(pq, (PQNode){(int64_t)dist_esagoni(xp, yp, xd, yd), xp, yp});

    while (!pq_is_empty(pq)) {
        PQNode current = pq_pop(pq);
        uint16_t ux = current.x, uy = current.y;
        int64_t cost_so_far = distances[ux * map_rows + uy];

        //ERRORE in EDGE CASES dovuto a questo
        //if (ux == xd && uy == yd) break;

        // La riga seguente può essere commentata se si sospetta un'euristica inconsistente
        if (current.priority > cost_so_far + dist_esagoni(ux, uy, xd, yd)) continue;

        Hexagon* u_hex = &map[ux][uy];
        if (u_hex->cost > 0) {
            // Esplorazione via terra
            int directions[6][2][2] = {
                {{1, 0}, {1, -1}}, {{1, 1}, {1, 0}}, {{0, 1}, {0, 1}},
                {{-1, 1}, {-1, 0}}, {{-1, 0}, {-1, -1}}, {{0, -1}, {0, -1}}
            };
            for (int i = 0; i < 6; i++) {
                int offset_col = directions[i][uy % 2][0];
                int offset_row = directions[i][uy % 2][1];
                uint16_t vx = ux + offset_col;
                uint16_t vy = uy + offset_row;

                if (is_valid(vx, vy)) {
                    int64_t new_cost = cost_so_far + u_hex->cost;
                    if (new_cost < distances[vx * map_rows + vy]) {
                        distances[vx * map_rows + vy] = new_cost;
                        // ===== INIZIO MODIFICA: Salva il genitore e il tipo di mossa =====
                        parent[vx * map_rows + vy] = (Point){ux, uy};
                        move_type[vx * map_rows + vy] = 'L'; // 'L' per Land (Terra)
                        // ======================== FINE MODIFICA ========================
                        pq_push(pq, (PQNode){new_cost + dist_esagoni(vx, vy, xd, yd), vx, vy});
                    }
                }
            }

            // Esplorazione via aerea
            for (int i = 0; i < u_hex->num_air_routes; i++) {
                AirRoute* route = &u_hex->air_routes[i];
                if (route->cost > 0) {
                    int64_t new_cost = cost_so_far + route->cost;
                    if (new_cost < distances[route->dest_x * map_rows + route->dest_y]) {
                        distances[route->dest_x * map_rows + route->dest_y] = new_cost;
                        // ===== INIZIO MODIFICA: Salva il genitore e il tipo di mossa =====
                        parent[route->dest_x * map_rows + route->dest_y] = (Point){ux, uy};
                        move_type[route->dest_x * map_rows + route->dest_y] = 'A'; // 'A' per Air (Aereo)
                        // ======================== FINE MODIFICA ========================
                        pq_push(pq, (PQNode){new_cost + dist_esagoni(route->dest_x, route->dest_y, xd, yd), route->dest_x, route->dest_y});
                    }
                }
            }
        }
    }

    pq_destroy(pq);

    int64_t final_cost = distances[xd * map_rows + yd];

    //DEBUG PRINTF
    // ===== INIZIO MODIFICA: Ricostruisci e stampa il percorso se trovato =====
    if (final_cost != LLONG_MAX) {
        fprintf(stderr, "DEBUG: Percorso trovato con costo totale: %ld\n", final_cost);
        Point path[map_size];
        int path_len = 0;
        uint16_t curr_x = xd, curr_y = yd;

        // Ricostruisci il percorso dalla fine alla partenza
        while (curr_x != xp || curr_y != yp) {
            path[path_len++] = (Point){curr_x, curr_y};
            Point p = parent[curr_x * map_rows + curr_y];
            curr_x = p.x;
            curr_y = p.y;
        }
        path[path_len++] = (Point){xp, yp};

        // Stampa il percorso dalla partenza alla fine
        fprintf(stderr, "DEBUG: Sequenza del percorso:\n");
        for (int i = path_len - 1; i >= 0; --i) {
            uint16_t px = path[i].x;
            uint16_t py = path[i].y;
            char mt = move_type[px * map_rows + py];

            if (i == path_len - 1) {
                fprintf(stderr, " -> Partenza da (%u, %u)\n", px, py);
            } else {
                Point prev_p = path[i+1];
                if (mt == 'L') {
                    fprintf(stderr, " -> Spostamento via terra da (%u, %u) a (%u, %u)\n", prev_p.x, prev_p.y, px, py);
                } else if (mt == 'A') {
                    fprintf(stderr, " -> Decollo da (%u, %u) e atterraggio a (%u, %u)\n", prev_p.x, prev_p.y, px, py);
                }
            }
        }
    } else {
         fprintf(stderr, "DEBUG: Nessun percorso trovato.\n");
    }
    //======================== FINE MODIFICA ========================

    printf("%ld\n", final_cost == LLONG_MAX ? -1 : final_cost);

    cache_put(xp, yp, distances);

    //Utili alla stampa di DEBUG
    free(parent);
    free(move_type);
}*/

void do_travel_cost(uint16_t xp, uint16_t yp, uint16_t xd, uint16_t yd) {
    if (!is_valid(xp, yp) || !is_valid(xd, yd)) {
        printf("-1\n");
        return;
    }
    if (xp == xd && yp == yd) {
        printf("0\n");
        return;
    }

    int64_t* cached_distances = cache_get(xp, yp);
    if (cached_distances) {
        int64_t cost = cached_distances[xd * map_rows + yd];
        printf("%ld\n", cost == LLONG_MAX ? -1 : cost);
        return;
    }

    size_t map_size = map_cols * map_rows;
    int64_t* distances = (int64_t*)malloc(map_size * sizeof(int64_t));

    for (size_t i = 0; i < map_size; ++i) {
        distances[i] = LLONG_MAX;
    }
    distances[xp * map_rows + yp] = 0;

    PriorityQueue* pq = pq_create(128);
    pq_push(pq, (PQNode){0, xp, yp}); // Usa 0 come priorità iniziale invece dell'euristica

    while (!pq_is_empty(pq)) {
        PQNode current = pq_pop(pq);
        uint16_t ux = current.x, uy = current.y;
        int64_t cost_so_far = distances[ux * map_rows + uy];

        if (ux == xd && uy == yd) break;

        // Rimuovi questo controllo che può causare problemi con l'euristica
        // if (current.priority > cost_so_far + dist_esagoni(ux, uy, xd, yd)) continue;

        Hexagon* u_hex = &map[ux][uy];
        if (u_hex->cost > 0) {
            // CORREZIONE 1: Direzioni corrette per griglia odd-r
            // [direzione][parità_riga][x_o_y]
            int directions[6][2][2] = {
                {{1, 0}, {1, 0}},   // Est
                {{0, 1}, {1, 1}},   // Sud-Est
                {{-1, 1}, {0, 1}},  // Sud-Ovest
                {{-1, 0}, {-1, 0}}, // Ovest
                {{-1, -1}, {0, -1}}, // Nord-Ovest
                {{0, -1}, {1, -1}}   // Nord-Est
            };

            for (int i = 0; i < 6; i++) {
                int offset_col = directions[i][uy % 2][0];
                int offset_row = directions[i][uy % 2][1];

                int new_x = (int)ux + offset_col;
                int new_y = (int)uy + offset_row;

                // Controlla bounds con casting sicuro
                if (new_x >= 0 && new_y >= 0 && new_x < (int)map_cols && new_y < (int)map_rows) {
                    uint16_t vx = (uint16_t)new_x;
                    uint16_t vy = (uint16_t)new_y;

                    Hexagon* v_hex = &map[vx][vy];
                    if (v_hex->cost > 0) { // Controlla che la destinazione sia attraversabile
                        int64_t new_cost = cost_so_far + u_hex->cost;
                        if (new_cost < distances[vx * map_rows + vy]) {
                            distances[vx * map_rows + vy] = new_cost;
                            pq_push(pq, (PQNode){new_cost + dist_esagoni(vx, vy, xd, yd), vx, vy});
                        }
                    }
                }
            }

            // CORREZIONE 2: Costo delle rotte aeree corretto
            for (int i = 0; i < u_hex->num_air_routes; i++) {
                AirRoute* route = &u_hex->air_routes[i];
                Hexagon* dest_hex = &map[route->dest_x][route->dest_y];

                // Il costo totale è: costo_partenza + costo_rotta + costo_destinazione
                // Ma dalla logica sembra che il costo della rotta includa già tutto
                // Prova prima con solo il costo della rotta:
                int64_t new_cost = cost_so_far + route->cost;

                if (new_cost < distances[route->dest_x * map_rows + route->dest_y]) {
                    distances[route->dest_x * map_rows + route->dest_y] = new_cost;
                    pq_push(pq, (PQNode){new_cost + dist_esagoni(route->dest_x, route->dest_y, xd, yd),
                                        route->dest_x, route->dest_y});
                }
            }
        }
    }

    pq_destroy(pq);

    int64_t final_cost = distances[xd * map_rows + yd];
    printf("%ld\n", final_cost == LLONG_MAX ? -1 : final_cost);
    cache_put(xp, yp, distances);
}

void cleanup_resources() {
    if (map) {
        for (uint32_t i = 0; i < map_cols; i++) {
            free(map[i]);
        }
        free(map);
        map = NULL;
    }
    destroy_cache();
}

// ============================================================================
// 5. MAIN FUNCTION (PROGRAM ENTRYPOINT)
// ============================================================================

int main() {
    char command[32];
    while (scanf("%s", command) != EOF) {
        if (strcmp(command, "init") == 0) {
            uint32_t cols, rows;
            (void)scanf("%u %u", &cols, &rows);
            do_init(cols, rows);
        } else if (strcmp(command, "change_cost") == 0) {
            uint16_t x, y; int v, r;
            (void)scanf("%hu %hu %d %d", &x, &y, &v, &r);
            do_change_cost(x, y, v, r);
        } else if (strcmp(command, "toggle_air_route") == 0) {
            uint16_t x1, y1, x2, y2;
            (void)scanf("%hu %hu %hu %hu", &x1, &y1, &x2, &y2);
            do_toggle_air_route(x1, y1, x2, y2);
        } else if (strcmp(command, "travel_cost") == 0) {
            uint16_t xp, yp, xd, yd;
            (void)scanf("%hu %hu %hu %hu", &xp, &yp, &xd, &yd);
            do_travel_cost(xp, yp, xd, yd);
        }
    }
    cleanup_resources();
    return 0;
}