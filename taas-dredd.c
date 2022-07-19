/* ============================================================================================================== */
/* == BEGIN FILE ================================================================================================ */
/* ============================================================================================================== */
/*
 ============================================================================
 Name        : taas-harper.c
 Author      : Matthias Thimm
 Version     : 1.0
 Copyright   : GPL3
 Description : The taas-dredd solver for abstract argumentation.

============================================================================
*/
#define COMPUTATION_FINISHED 0
#define COMPUTATION_ABORTED__ANSWER_YES 1
#define COMPUTATION_ABORTED__ANSWER_NO  2
#define COMPUTATION_ABORTED__ANSWER_EMPTYSET  3
#define COMPUTATION_ABORTED__ANSWER_EMPTYEMPTYSET  4
#define COMPUTATION_FINISHED__EMPTY_GROUNDED  5
#define COMPUTATION_FINISHED__NONEMPTY_GROUNDED  6
#define COMPUTATION_FINISHED__ANSWER_NO  7

#define TRUE 1
#define FALSE 0
int CFALSE = FALSE;
int CTRUE = TRUE;

// failed labels
#define FAILED_LAB_NOTHING 0
#define FAILED_LAB_IN 1
#define FAILED_LAB_OUT 2
#define FAILED_LAB_IN_OUT 3
#define FAILED_LAB_UNDECIDED 4
#define FAILED_LAB_IN_UNDECIDED 5
#define FAILED_LAB_OUT_UNDECIDED 6
#define FAILED_LAB_IN_OUT_UNDECIDED 7
/* ============================================================================================================== */
/* ============================================================================================================== */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <time.h>
#include <sys/types.h>

#include "util/bitset.c"
#include "util/linkedlist.c"
#include "util/miscutil.c"
#include "util/hashtable.c"
#include "util/binaryheap.c"
#include "util/raset.c"

#include "taas/taas_aaf.c"
#include "taas/taas_inout.c"
#include "taas/taas_labeling.c"
#include "taas/taas_labeling_set.c"
#include "taas/taas_basics.c"

#include "util/graph.c"
/* ============================================================================================================== */
/* ============================================================================================================== */

int* hvalues;

/**
 * let d_i be the number of paths of length i that end/start in argument "arg"
 * (ending == TRUE means ending paths; ending == FALSE means starting paths);
 * then this function return \sum_i=1^depth weight^i * d_i
 */
int __heuristic__number_of_paths_weighted(struct AAF* aaf, int* all_arguments, int arg, int depth, char ending, double weight){
  int result = 0;
  struct LinkedList* q_args = malloc(sizeof(struct LinkedList));
  struct LinkedList* q_distances = malloc(sizeof(struct LinkedList));
  llist__init(q_args);
  llist__init(q_distances);
  llist__push(q_args,&arg);
  int* val = malloc(sizeof(int));
  *val = 0;
  llist__push(q_distances,val);
  while(q_args->length > 0){
    int* arg2 = llist__pop(q_args);
    int* val2 = llist__pop(q_distances);
    // we scale by 1/pow(weight,depth) to get integers, should be optimised
    if(*val2 > 0)
      result += round(pow(weight,*val2) * 1/pow(weight,depth));
    if(*val2 < depth){
      struct LinkedList* list = ending ? aaf->parents : aaf->children;
      for(struct LinkedListNode* node = list[*arg2].root; node != NULL; node = node->next){
        val = malloc(sizeof(int));
        *val = *val2+1;
        llist__push(q_args,(int*)node->data);
        llist__push(q_distances,val);
      }
    }
    free(val2);
  }
  llist__destroy_without_data(q_args);
  llist__destroy(q_distances);
  return result;
}

/**
 * initialises heuristic values of arguments.
 */
void init_hvalues(struct TaskSpecification *task, struct AAF* aaf, int* all_arguments){
  hvalues = malloc(aaf->number_of_arguments * sizeof(int));
  // initialise heuristic values
  for(int i = 0; i < aaf->number_of_arguments; i++)
    hvalues[i] = 0;
  for(int i = 0; i < task->number_of_additional_arguments; i++){
      if(strcmp(task->additional_keys[i],"-h_constant") == 0){
        // constant heuristic: all arguments get value 0
        // nothing to be done as this is the default option
      }else if(strcmp(task->additional_keys[i],"-h_in_degree") == 0){
        // in_degree heuristic: all arguments get their (inverted) in-degree
        // additional argument gives the multiplicator of this heuristic (if != 0)
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        for(int j = 0; j < aaf->number_of_arguments; j++)
          hvalues[j] += multiplicator * (aaf->number_of_arguments - aaf->parents[j].length);
      }else if(strcmp(task->additional_keys[i],"-h_out_degree") == 0){
        // out_degree heuristic: all arguments get their (inverted) out-degree
        // additional argument gives the multiplicator of this heuristic (if !=0)
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        for(int j = 0; j < aaf->number_of_arguments; j++)
          hvalues[j] += multiplicator * (aaf->number_of_arguments - aaf->children[j].length);
      }else if(strcmp(task->additional_keys[i],"-h_scc") == 0){
        // SCC heuristic: arguments get a heuristic value depending on their
        // SCC (arguments in initial SCCs get minimal value, arguments in
        // later SCCs get higher values)
        // additional argument gives the multiplicator of this heuristic (if !=0)
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        struct LinkedList* sccs = scc__compute_strongly_connected_components(aaf,all_arguments);
        int value = sccs->length;
        for(struct LinkedListNode* scc = sccs->root; scc != NULL; scc = scc->next){
          for(struct LinkedListNode* v = (*(struct LinkedList*)scc->data).root; v != NULL; v = v->next)
            hvalues[*(int*)v->data] += multiplicator * value;
          value--;
        }
      }else if(strcmp(task->additional_keys[i],"-h_graded") == 0){
        // Graded heuristic: each argument receives a value of 1; then this value is
        // updated by subtracting the values of each attacker; this process is repeated for
        // <param> number of iterations. The final heuristic value is determined by multiplying
        // with -1
        // additional argument gives the multiplicator of this heuristic (if !=0)
        // needs additional paramenter "-h_graded_iterations" to give the number of
        // iterations
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        int* hvalues_tmp1 = malloc(aaf->number_of_arguments * sizeof(int));
        int* hvalues_tmp2 = malloc(aaf->number_of_arguments * sizeof(int));
        int h_iterations;
        for(int j = 0; j < task->number_of_additional_arguments; j++){
          if(strcmp(task->additional_keys[j],"-h_graded_iterations") == 0)
            h_iterations = atoi(task->additional_values[j]);
        }
        for(int j = 0; j < aaf->number_of_arguments; j++){
          hvalues_tmp1[j] = 1;
        }
        for(int j = 0; j < h_iterations; j++){
          for(int k = 0; k < aaf->number_of_arguments; k++){
            hvalues_tmp2[k] = hvalues_tmp1[k];
            for(struct LinkedListNode* node = aaf->parents[k].root; node != NULL; node = node->next)
              hvalues_tmp2[k] -= hvalues_tmp1[*(int*)node->data];
          }
          for(int k = 0; k < aaf->number_of_arguments; k++){
            hvalues_tmp1[k] = hvalues_tmp2[k];
            for(struct LinkedListNode* node = aaf->parents[k].root; node != NULL; node = node->next)
              hvalues_tmp1[k] -= hvalues_tmp2[*(int*)node->data];
          }
        }
        for(int j = 0; j < aaf->number_of_arguments; j++){
          hvalues[j] -= multiplicator * hvalues_tmp1[j];
        }
        free(hvalues_tmp1);
        free(hvalues_tmp2);
      }else if(strcmp(task->additional_keys[i],"-h_paths_starting") == 0){
        // Path+ heuristic:
        // - \sum_i=1^<param1> <param2>^i * number_of_paths_of_length_i_starting_in_arg
        // additional argument gives the multiplicator of this heuristic (if !=0)
        // needs two additional arguments "-h_paths_starting_max_length" indicating the max length of paths
        // considered and "-h_paths_starting_weight" the weight of paths.
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        int h_max_length;
        double h_weight;
        for(int j = 0; j < task->number_of_additional_arguments; j++){
          if(strcmp(task->additional_keys[j],"-h_paths_starting_max_length") == 0)
            h_max_length = atoi(task->additional_values[j]);
          if(strcmp(task->additional_keys[j],"-h_paths_starting_weight") == 0)
            h_weight = atof(task->additional_values[j]);
        }
        for(int j = 0; j < aaf->number_of_arguments; j++){
          hvalues[j] -= multiplicator * __heuristic__number_of_paths_weighted(aaf,all_arguments, j, h_max_length, FALSE, h_weight);
        }
      }else if(strcmp(task->additional_keys[i],"-h_paths_ending") == 0){
        // Path- heuristic:
        // - \sum_i=1^<param1> <param2>^i * number_of_paths_of_length_i_ending_in_arg
        // additional argument gives the multiplicator of this heuristic (if !=0)
        // needs two additional arguments "-h_path_ending_max_length" indicating the max length of paths
        // considered and "-h_path_ending_weight" the weight of paths.
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        int h_max_length;
        double h_weight;
        for(int j = 0; j < task->number_of_additional_arguments; j++){
          if(strcmp(task->additional_keys[j],"-h_paths_ending_max_length") == 0)
            h_max_length = atoi(task->additional_values[j]);
          if(strcmp(task->additional_keys[j],"-h_paths_ending_weight") == 0)
            h_weight = atof(task->additional_values[j]);
        }
        for(int j = 0; j < aaf->number_of_arguments; j++){
          hvalues[j] -= multiplicator * __heuristic__number_of_paths_weighted(aaf,all_arguments, j, h_max_length, TRUE, h_weight);
        }
      }else if(strcmp(task->additional_keys[i],"-h_deg_rat") == 0){
        // Deg_rat heuristic:
        // - in_degree+<param1> / out_degree+<param1>
        // additional argument gives the multiplicator of this heuristic (if !=0)
        // needs additional paramenter "-h_deg_rat_epsilon"
        int hparam = atoi(task->additional_values[i]);
        int multiplicator = hparam != 0 ? hparam*aaf->number_of_arguments : 1;
        float h_epsilon;
        for(int j = 0; j < task->number_of_additional_arguments; j++){
          if(strcmp(task->additional_keys[j],"-h_deg_rat_epsilon") == 0)
            h_epsilon = atof(task->additional_values[j]);
        }
        for(int i = 0; i < aaf->number_of_arguments; i++){
            hvalues[i] -= multiplicator * (aaf->parents[i].length + h_epsilon) / (aaf->children[i].length + h_epsilon) ;
        }
      }
  }
  // for debugging: print all heuristic values
  //for(int i = 0; i < aaf->number_of_arguments; i++){
  //  printf("%s -> %i\n",aaf->ids2arguments[i], hvalues[i]);
  //}
}

/**
 * Return the heuristic value of the given argument "arg" wrt.
 * the argumentation graph aaf and the current labeling lab.
 * Lower values indicate higher priority
 */
int hvalue(int arg, struct AAF* aaf, struct Labeling* lab){
  return hvalues[arg];
}

/**
 * Returns the next possible label for the given arguments where
 * "failed_labels" lists the already tried labels. It is assumed that
 * there is always at least one not tried label.
 */
int next_label(int arg, int failed_labels, char isStableSemantics){
  //for stable semantics, only IN and OUT are valid labels
  if(isStableSemantics){
    if(failed_labels ==  FAILED_LAB_NOTHING || failed_labels == FAILED_LAB_OUT)
      return LAB_IN;
    return LAB_OUT;
  }
  // for now, we just use the static order IN, OUT, UNDECIDED
  if(failed_labels == FAILED_LAB_NOTHING || failed_labels == FAILED_LAB_OUT ||
    failed_labels == FAILED_LAB_UNDECIDED || failed_labels == FAILED_LAB_OUT_UNDECIDED)
    return LAB_IN;
  if(failed_labels == FAILED_LAB_IN || failed_labels == FAILED_LAB_IN_UNDECIDED)
    return LAB_OUT;
  return LAB_UNDEC;
}

/**
 * Sets the argument to the given label and sets its status to
 * "inferred" (and making the necessary modifications),
 */
void set_inferred(struct LinkedList* arguments_labelled,
    struct LinkedList* arguments_labelled_inferred,
    int* argument,
    int label,
    struct Labeling* lab,
    char* failed_labels,
    struct BinaryHeap* arguments_to_label,
    struct RaSet* arguments_to_be_checked,
    char isStableSemantics){
  llist__push(arguments_labelled, argument);
  llist__push(arguments_labelled_inferred, &CTRUE);
  taas__lab_set_label(lab,*argument,label);
  failed_labels[*argument] = isStableSemantics? FAILED_LAB_IN_OUT : FAILED_LAB_IN_OUT_UNDECIDED;
  raset__add(arguments_to_be_checked,*argument);
  binaryheap__remove(arguments_to_label,argument);
}

void print_argument_stack(struct LinkedList* stack, struct AAF* aaf){
  printf("[");
  char isFirst = CTRUE;
  for(struct LinkedListNode* node = stack->root; node != NULL; node = node->next){
    if(isFirst){
      printf("%s", aaf->ids2arguments[*(int*) node->data]);
      isFirst = CFALSE;
    }else printf(",%s", aaf->ids2arguments[*(int*) node->data]);
  }
  printf("]");
}

/**
 * Solve SE-PR,EE-PR,DC-PR,DS-PR,EE-CO,DC-CO,SE-ST,EE-ST,DC-ST,DS-ST
 */
void solve(struct TaskSpecification *task, struct AAF* aaf, struct Labeling* lab){
  // in order to have pointers to the arguments
  int* all_arguments = malloc(aaf->number_of_arguments * sizeof(int));
  for(int i = 0; i < aaf->number_of_arguments; i++)
    all_arguments[i] = i;
  // init heuristic
  init_hvalues(task,aaf,all_arguments);
  // check whether we have an enumeration problem
  char enumerate = FALSE;
  char enumerate_is_first = TRUE;
  if(strcmp(task->problem,"EE") == 0)
    enumerate = TRUE;
  if(enumerate)
    printf("[\n");
  // check whether we have a problem with preferred semantics (then we
  // have to ensure maximality in enumeration problems
  char isPreferred = strcmp(task->track,"SE-PR") == 0 || strcmp(task->track,"EE-PR") == 0 || strcmp(task->track,"DC-PR") == 0 || strcmp(task->track,"DS-PR") == 0;
  // check whether we have a problem with stable semantics (then the label UNDEC)
  // can be ignored
  char isStableSemantics = strcmp(task->track,"SE-ST") == 0 || strcmp(task->track,"EE-ST") == 0 || strcmp(task->track,"DC-ST") == 0 || strcmp(task->track,"DS-ST") == 0;
  char failed_all_label = isStableSemantics ? FAILED_LAB_IN_OUT : FAILED_LAB_IN_OUT_UNDECIDED;
  // check whether we have a decision problem (note that DS-CO is already solved)
  char decide_skeptical = FALSE;
  char decide_credulous = FALSE;
  char decide_skeptical_stable = strcmp(task->track,"DS-ST") == 0;
  // if we have DS-ST we have to do two runs
  char decide_skeptical_stable_first_run = TRUE;
  if(strcmp(task->problem,"DS") == 0){
    decide_skeptical = TRUE;
  }
  if(strcmp(task->problem,"DC") == 0){
    //for credulous inference we check whether there is a valid labelling that
    //makes the query argument in
    decide_credulous = TRUE;
    taas__lab_set_label(lab, task->arg, LAB_IN);
  }
  // maybe we have to store all preferred labelings
  struct LabelingSet* labset_pref;
  if(isPreferred && (enumerate || decide_skeptical))
    labset_pref = taas__labset_init_empty();
  // models a stack of the arguments already labelled in the corresponding order
  struct LinkedList* arguments_labelled = malloc(sizeof(struct LinkedList));
  llist__init(arguments_labelled);
  // keeps track of whether the corresponding argument in the previous stack
  // has its value inferred (TRUE) or selected (FALSE)
  struct LinkedList* arguments_labelled_inferred = malloc(sizeof(struct LinkedList));
  llist__init(arguments_labelled_inferred);
  // keeps track of the arguments still to be labelled
  struct BinaryHeap* arguments_to_label = malloc(sizeof(struct BinaryHeap));
  // keeps track of failed labels
  char* failed_labels = malloc(aaf->number_of_arguments * sizeof(char));
  for(int i = 0; i < aaf->number_of_arguments; i++)
    failed_labels[i] = FAILED_LAB_NOTHING;
  // populate arguments_to_label (those are the ones labeled undec in the grounded labelling)
  // also set their label in lab to unlabeled
  binaryheap__init(arguments_to_label, aaf->number_of_arguments);
  for(int i = 0; i < aaf->number_of_arguments; i++){
    if(taas__lab_get_label(lab,all_arguments[i]) == LAB_UNDEC){
      binaryheap__insert(arguments_to_label, &all_arguments[i], hvalue(all_arguments[i],aaf,lab));
      taas__lab_set_label(lab,all_arguments[i],LAB_UNLABELED);
    }
  }
  //-------------------
  // OUTER LOOP - BEGIN
  //-------------------
  int* current_argument;
  int nextLabel;
  int noLabelingFound = FALSE;
  char backtrack;
  struct RaSet* arguments_to_be_checked = raset__init_empty(aaf->number_of_arguments);
  do{
      //------------------
      // MAIN LOOP - BEGIN
      //------------------
      while(arguments_to_label->length > 0){
        current_argument = binaryheap__extract_minimum(arguments_to_label);
        // if we already tried all labelings for current_argument we are finished
        if(isStableSemantics){
          if(failed_labels[*current_argument] == FAILED_LAB_IN_OUT){
            noLabelingFound = TRUE;
            break;
          }
        }else{
          if(failed_labels[*current_argument] == FAILED_LAB_IN_OUT_UNDECIDED){
            noLabelingFound = TRUE;
            break;
          }
        }
        llist__push(arguments_labelled, current_argument);
        llist__push(arguments_labelled_inferred, &CFALSE);
        nextLabel = next_label(*current_argument,failed_labels[*current_argument],isStableSemantics);
        // for debugging: print current labeling, the selected argument, its label, and the current labelled stack
        //printf("%s ",taas__lab_print_as_labeling(lab,aaf));
        //printf(" %s=%i ",aaf->ids2arguments[*current_argument], nextLabel);
        //print_argument_stack(arguments_labelled,aaf);
        //printf(" -- ");
        //for(int i = 0; i < aaf->number_of_arguments; i++)
        //   printf("%s:%i ",aaf->ids2arguments[i], failed_labels[i]);
        //printf("\n");
        // --
        taas__lab_set_label(lab,*current_argument,nextLabel);
        failed_labels[*current_argument] += nextLabel;
        // clear arguments_to_be_checked
        raset__reset(arguments_to_be_checked);
        // add current argument
        raset__add(arguments_to_be_checked,*current_argument);
        backtrack = FALSE;
        while(arguments_to_be_checked->number_of_elements > 0){
          int argument_to_be_checked = raset__get(arguments_to_be_checked,0);
          raset__remove(arguments_to_be_checked,argument_to_be_checked);
          if(taas__lab_get_label(lab, argument_to_be_checked) == LAB_IN){
            // if argument_to_be_checked is set to IN,
            // 	1.) all its parents have to be OUT
            //		1.1.) if there is at least one parent already labeled IN or UNDECIDED, we have a contradiction
            // 	2.) all its children have to be OUT
            //		2.1.) if there is at least one child already labeled IN or UNDECIDED, we have a contradiction
            // every unlabelled parent/child of argument_to_be_checked is labelled OUT and added to arguments_to_be_checked
            //check parents
            for(struct LinkedListNode* node = aaf->parents[argument_to_be_checked].root; node != NULL; node = node->next){
              int* parent = (int*)node->data;
              // if there is a parent of argument_to_be_checked labelled IN or UNDECIDED -> contradiction
              if(taas__lab_get_label(lab,*parent) == LAB_IN || taas__lab_get_label(lab,*parent) == LAB_UNDEC){
                backtrack = TRUE;
                break;
              }
              // if there is an unlabelled parent -> label it OUT
              if(taas__lab_get_label(lab,*parent) == LAB_UNLABELED){
                set_inferred(arguments_labelled,arguments_labelled_inferred,parent,LAB_OUT,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
                // for debugging
                //print_argument_stack(arguments_labelled,aaf);
                //printf("  i OUT: %s\n",aaf->ids2arguments[*parent]);
                // --
              }
            }
            //check children
            for(struct LinkedListNode* node = aaf->children[argument_to_be_checked].root; node != NULL; node = node->next){
              int* child = (int*)node->data;
              // if there is a child of argument_to_be_checked labelled IN or UNDECIDED -> contradiction
              if(taas__lab_get_label(lab,*child) == LAB_IN || taas__lab_get_label(lab,*child) == LAB_UNDEC){
                backtrack = TRUE;
                break;
              }
              // if there is an unlabelled child -> label it OUT
              if(taas__lab_get_label(lab,*child) == LAB_UNLABELED){
                set_inferred(arguments_labelled,arguments_labelled_inferred,child,LAB_OUT,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
                // for debugging
                //print_argument_stack(arguments_labelled,aaf);
                //printf("  i OUT: %s\n",aaf->ids2arguments[*child]);
                // --
              }
            }
          }else if(taas__lab_get_label(lab, argument_to_be_checked) == LAB_OUT){
            // if argument_to_be_checked is set to OUT,
            //	1.) at least one parent has to be IN
            //		1.1.) if all parents are already labeled and none of it is labeled IN, we have a contradiction
            //		1.2.) if all but one parent are already labeled with OUT or UNDECIDED, the remaining parent has
            //				to be labeled IN and is added to arguments_to_be_checked
            //		1.3.) if there are at least two unlabeled parents or an IN-labeled parent, nothing more can be done
            // 	2.) a child may be labeled, if now all its parents are labeled
            //		2.1.) if a child already has a label IN, then nothing is to be done
            //		2.2.) if now all parents of a child are labeled OUT, the child will be labeled IN and added to arguments_to_be_checked
            //      		(if it already has another label, we have a contradiction)
            //     	2.3.) if now all parents of a child are labeled OUT and UNDECIDED (at least one of the latter)
            //				then the child will be labeled UNDECIDED and added to check (if it already has another label, we have a contradiction)
            //check parents
            char has_in_labeled_parent = FALSE;
            char has_at_least_one_unlabeled_parent = FALSE;
            char has_more_than_one_unlabeled_parent = FALSE;
            int* the_only_one_unlabeled_parent;
            for(struct LinkedListNode* node = aaf->parents[argument_to_be_checked].root; node != NULL; node = node->next){
              int* parent = (int*)node->data;
              int label = taas__lab_get_label(lab,*parent);
              if(label == LAB_IN){
                has_in_labeled_parent = TRUE;
              }else{
                if(label == LAB_UNLABELED){
                  if(!has_more_than_one_unlabeled_parent && !has_at_least_one_unlabeled_parent){
                    the_only_one_unlabeled_parent = parent;
                    has_at_least_one_unlabeled_parent = TRUE;
                  }else if(has_at_least_one_unlabeled_parent)
                    has_more_than_one_unlabeled_parent = TRUE;
                }
              }
            }
            if(!has_at_least_one_unlabeled_parent && !has_more_than_one_unlabeled_parent && !has_in_labeled_parent){
              backtrack = TRUE;
              break;
            }
            if(has_at_least_one_unlabeled_parent && !has_more_than_one_unlabeled_parent && !has_in_labeled_parent){
              set_inferred(arguments_labelled,arguments_labelled_inferred,the_only_one_unlabeled_parent,LAB_IN,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
              // for debugging
              //print_argument_stack(arguments_labelled,aaf);
              //printf(" i IN: %s\n",aaf->ids2arguments[*the_only_one_unlabeled_parent]);
              // --
            }
            //check children
            for(struct LinkedListNode* node = aaf->children[argument_to_be_checked].root; node != NULL; node = node->next){
              int* child = (int*)node->data;
              int label = taas__lab_get_label(lab,*child);
              if(label == LAB_IN)
                continue;
              // check parents of child
              char one_parent_in = FALSE;
              char one_parent_undecided = FALSE;
              char one_parent_unlabeled = FALSE;
              for(struct LinkedListNode* node2 = aaf->parents[*child].root; node2 != NULL; node2 = node2->next){
                int* parchild = (int*)node2->data;
                int label2 = taas__lab_get_label(lab,*parchild);
                if(label2 == LAB_IN)
                  one_parent_in = TRUE;
                if(label2 == LAB_UNLABELED)
                  one_parent_unlabeled = TRUE;
                if(label2 == LAB_UNDEC)
                  one_parent_undecided = TRUE;
              }
              if(!one_parent_in && !one_parent_unlabeled && !one_parent_undecided && label != LAB_UNLABELED){
                backtrack = TRUE;
                break;
              }else if(!one_parent_in && !one_parent_unlabeled && !one_parent_undecided){
                set_inferred(arguments_labelled,arguments_labelled_inferred,child,LAB_IN,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
                // for debugging
                //print_argument_stack(arguments_labelled,aaf);
                //printf(" i IN: %s\n",aaf->ids2arguments[*child]);
                // --
              }else if(!one_parent_unlabeled && one_parent_undecided && !one_parent_in && label == LAB_OUT){
                backtrack = TRUE;
                break;
              }else if(!one_parent_unlabeled && one_parent_undecided && !one_parent_in && label == LAB_UNLABELED){
                set_inferred(arguments_labelled,arguments_labelled_inferred,child,LAB_UNDEC,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
                // for debugging
                //print_argument_stack(arguments_labelled,aaf);
                //printf(" i UNDEC: %s\n",aaf->ids2arguments[*child]);
                // --
              }
            }
          }else if(taas__lab_get_label(lab, argument_to_be_checked) == LAB_UNDEC){
            // if argument_to_be_checked is set to UNDECIDED
            //	1.) no parent can be labeled IN and at least one parent has to be labeled UNDECIDED
            //		1.1.) if there is parent already labeled IN, we have a contradiction
            //		1.2.) if all parents are labeled OUT, we have a contradiction
            //		1.3.) if all but one parent is labeled OUT, then the remaining parent has to be labeled UNDECIDED and is added to arguments_to_be_checked
            //		1.4.) if there are at least two unlabeled parents or a parent labeled UNDECIDED, nothing more can be done
            // 2.) no child can be labeled IN,
            //		2.1.) if there is a child already labeled IN, we have a contradiction
            //		2.2.) if there is a child labeled OUT add it to arguments_to_be_checked
            //			2.2.1) if all its parents are labeled OUT or UNDECIDED, we have a contradiction
            //			2.2.2) if all but one of its parents are labeled OUT and UNDECIDED,
            //					then the remaining parent has to be labeled IN and is added to arguments_to_be_checked
            //		2.3.) if now all of its parent are labeled OUT or UNDECIDED and the
            //				child is not yet labeled UNDECIDED, the child gets labeled UNDECIDED and is added to arguments_to_be_checked
            //check parents
            char has_undec_parent = FALSE;
            char has_at_least_one_unlabeled_parent = FALSE;
            char has_more_than_one_unlabeled_parent = FALSE;
            int* the_only_one_unlabeled_parent;
            for(struct LinkedListNode* node = aaf->parents[argument_to_be_checked].root; node != NULL; node = node->next){
              int* parent = (int*)node->data;
              int label = taas__lab_get_label(lab,*parent);
              if(label == LAB_IN){
                backtrack = TRUE;
                break;
              }else if(label == LAB_UNDEC){
                has_undec_parent = TRUE;
              }else if(label == LAB_UNLABELED){
                if(!has_at_least_one_unlabeled_parent && !has_more_than_one_unlabeled_parent){
                  has_at_least_one_unlabeled_parent = TRUE;
                  the_only_one_unlabeled_parent = parent;
                }else if(has_at_least_one_unlabeled_parent){
                  has_more_than_one_unlabeled_parent = TRUE;
                }
              }
            }
            if(!has_undec_parent && !has_at_least_one_unlabeled_parent && !has_more_than_one_unlabeled_parent){
              backtrack = TRUE;
              break;
            }
            if(!has_undec_parent && has_at_least_one_unlabeled_parent && !has_more_than_one_unlabeled_parent){
              set_inferred(arguments_labelled,arguments_labelled_inferred,the_only_one_unlabeled_parent,LAB_UNDEC,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
              // for debugging
              //print_argument_stack(arguments_labelled,aaf);
              //printf(" i UNDEC: %s\n",aaf->ids2arguments[*the_only_one_unlabeled_parent]);
              // --
            }
            //check children
            for(struct LinkedListNode* node = aaf->children[argument_to_be_checked].root; node != NULL; node = node->next){
              int* child = (int*)node->data;
              int label = taas__lab_get_label(lab,*child);
              if(label == LAB_IN){
                backtrack = TRUE;
                break;
              }else if(label == LAB_OUT){
                raset__add(arguments_to_be_checked,*child);
              }else if(label == LAB_UNLABELED){
                char must_label_undec = TRUE;
                  for(struct LinkedListNode* node2 = aaf->parents[*child].root; node2 != NULL; node2 = node2->next){
                    int* parchild = (int*)node2->data;
                    int label2 = taas__lab_get_label(lab,*parchild);
                    if(label2 == LAB_UNLABELED || label2 == LAB_IN){
                      must_label_undec = FALSE;
                      break;
                    }
                  }
                  if(must_label_undec){
                    set_inferred(arguments_labelled,arguments_labelled_inferred,child,LAB_UNDEC,lab,failed_labels,arguments_to_label,arguments_to_be_checked,isStableSemantics);
                    // for debugging
                    //print_argument_stack(arguments_labelled,aaf);
                    //printf(" i UNDEC: %s\n",aaf->ids2arguments[*child]);
                    // --
                  }
              }
            }
          }else{
            // this should not happen
            printf("?\n");
          }
        }
        if(backtrack){
          // remove all arguments labelled so far which either
          // had their value inferred or were we tried all labels (for the latter
          // remove the current value in failed_labels)
          int* arg; // the current argument
          int* inferred; //whether its label was inferred
          int failed; // the list of already failed labels
          int label; // the current label
          do{
              arg = (int*) llist__pop(arguments_labelled);
              // for debugging
              //printf("b: %s\n",aaf->ids2arguments[*arg]);
              // --
              inferred = (int*) llist__pop(arguments_labelled_inferred);
              binaryheap__insert(arguments_to_label, arg, hvalue(*arg,aaf,lab));
              failed = failed_labels[*arg];
              label = taas__lab_get_label(lab,*arg);
              if(failed == failed_all_label && arguments_labelled->length > 0){
                failed_labels[*arg] = FAILED_LAB_NOTHING;
              }
              taas__lab_set_label(lab,*arg,LAB_UNLABELED);
          }while((*inferred == TRUE || failed == failed_all_label) && arguments_labelled->length > 0);
        }
      }
      //------------------
      // MAIN LOOP - END
      //------------------
      if(decide_skeptical_stable){
        // special treatment for DS-ST as we have to do two runs
        if(decide_skeptical_stable_first_run && noLabelingFound){
          // there are no stable extensions -> all arguments are skeptically accepted
          printf("YES\n");
          break;
        }
        if(decide_skeptical_stable_first_run){
          // there are stable extensions -> prepare second run and look
          // whether there is a stable extension labeling the argument OUT.
          // for that reset all data structures
          int* arg;
          while(arguments_labelled->length > 0){
              arg = (int*) llist__pop(arguments_labelled);
              llist__pop(arguments_labelled_inferred);
              failed_labels[*arg] = FAILED_LAB_NOTHING;
              binaryheap__insert(arguments_to_label, arg, hvalue(*arg,aaf,lab));
              taas__lab_set_label(lab,*arg,LAB_UNLABELED);
          }
          //special case: there is only one stable labeling which is also the grounded labeling
          // in that case, if the argument is labelled IN answer is YES, otherwise NO;
          if(arguments_to_label->length == 0){
            if(bitset__get(lab->in,task->arg))
              printf("YES\n");
            else printf("NO\n");
            break;
          }
          binaryheap__remove(arguments_to_label, &task->arg);
          taas__lab_set_label(lab, task->arg, LAB_OUT);
          decide_skeptical_stable_first_run = FALSE;
        }else if(noLabelingFound){
            // there are no stable extensions where the argument is OUT
            printf("YES\n");
            break;
        }else{
          // there is a stable extension where the argument is OUT
          printf("NO\n");
          break;
        }
      }else{
        if(noLabelingFound){
          if(decide_credulous){
            printf("NO\n");
          }else if(decide_skeptical){
            printf("YES\n");
          }else if(enumerate)
            printf("]\n");
          else printf("NO\n");
          break;
        }else{
          if(decide_skeptical && isPreferred){
            if(noLabelingFound){
              printf("YES\n");
              break;
            }else if(!taas__labset_subcontains(labset_pref,lab)){
              if(!bitset__get(lab->in,task->arg)){
                printf("NO\n");
                break;
              }
              taas__labset_add(labset_pref,lab);
            }
          }else{
            if(decide_credulous){
              printf("YES\n");
            }else if(decide_skeptical){
              printf("NO\n");
            }else{
              //for complete semantics, just print the extension
              //for preferred semantics, check whether we already
              //have a super set
              if(isPreferred && enumerate){
                if(!taas__labset_subcontains(labset_pref,lab)){
                  taas__labset_add(labset_pref,lab);
                  if(enumerate_is_first)
                    enumerate_is_first = FALSE;
                  //else printf(",");
                  printf("%s\n",taas__lab_print(lab,aaf));
                }
              }else{
                if(enumerate && enumerate_is_first){
                  enumerate_is_first = FALSE;
                }else if(enumerate){
                  //printf(",");
                }
                printf("%s",taas__lab_print(lab,aaf));
                //if(!enumerate)
                printf("\n");
              }
            }
          }
        }
        if(enumerate && arguments_labelled->length == 0){
          printf("]\n");
          break;
        }else if(enumerate || (isPreferred && decide_skeptical)){
          //backtrack last step
          // remove all arguments labelled so far which either
          // had their value inferred or were we tried all labels (for the latter
          // remove the current value in failed_labels)
          int* arg; // the current argument
          int* inferred; //whether its label was inferred
          int failed; // the list of already failed labels
          int label; // the current label
          do{
              arg = (int*) llist__pop(arguments_labelled);
              // for debugging
              //printf("b: %s\n",aaf->ids2arguments[*arg]);
              // --
              inferred = (int*) llist__pop(arguments_labelled_inferred);
              binaryheap__insert(arguments_to_label, arg, hvalue(*arg,aaf,lab));
              failed = failed_labels[*arg];
              label = taas__lab_get_label(lab,*arg);
              if(failed == failed_all_label && arguments_labelled->length > 0){
                failed_labels[*arg] = FAILED_LAB_NOTHING;
              }
              taas__lab_set_label(lab,*arg,LAB_UNLABELED);
          }while((*inferred == TRUE || failed == failed_all_label) && arguments_labelled->length > 0);
        }else{
          break;
        }
      }
  }while(TRUE);
  // free some variables
  llist__destroy_without_data(arguments_labelled);
  llist__destroy_without_data(arguments_labelled_inferred);
  binaryheap__destroy(arguments_to_label);
  free(all_arguments);
  free(hvalues);
  return;
}


/* ============================================================================================================== */
int main(int argc, char *argv[]){
  // General solver information
	struct SolverInformation *info = taas__solverinformation(
			"taas-dredd v1.9 (2019-03-08)\nMatthias Thimm (thimm@uni-koblenz.de)",
			"[tgf]",
			"[SE-GR,EE-GR,DC-GR,DS-GR,SE-PR,EE-PR,DC-PR,DS-PR,SE-CO,EE-CO,DC-CO,DS-CO,SE-ST,EE-ST,DC-ST,DS-ST]"
		);
  return taas__solve(argc,argv,info,solve);
}

/* ============================================================================================================== */
/* == END FILE ================================================================================================== */
/* ============================================================================================================== */
