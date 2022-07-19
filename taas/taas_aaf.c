/* ============================================================================================================== */
/* == BEGIN FILE ================================================================================================ */
/* ============================================================================================================== */
/*
 ============================================================================
 Name        : taas_aaf.c
 Author      : Matthias Thimm
 Version     : 1.0
 Copyright   : GPL3
 Description : General functions on AAFs for taas solvers.
 ============================================================================
 */

struct AAF{
  /** Mapping internal argument identifiers (ints) to argument names **/
  char** ids2arguments;
  /** Mapping argument names to internal argument identifiers (ints)**/
  struct StringHashTable* arguments2ids;  
  /** The number of arguments. */
  int number_of_arguments;
  /** The number of attacks. */
  int number_of_attacks;
  /** Maps arguments to their children */
  struct LinkedList* children;
  /** Maps arguments to their parents */
  struct LinkedList* parents;
  /** The initial arguments (unattacked ones) */
  struct BitSet* initial;
  /** Self-attacking arguments */
  struct BitSet* loops;
};

void taas__aaf_destroy(struct AAF* aaf){
  for(int i = 0; i < aaf->number_of_arguments; i++)
		free(aaf->ids2arguments[i]);
	free(aaf->ids2arguments);
  llist__destroy(aaf->children);
  llist__destroy(aaf->parents);
	hash__destroy(aaf->arguments2ids);
  free(aaf);
}

// Returns TRUE iff i attacks j
int taas__aaf_isAttack(struct AAF* aaf, int i, int j){
  for(struct LinkedListNode* node = aaf->children[i].root; node != NULL; node = node->next)
    if(*(int*)node->data == j)
      return TRUE;
  return FALSE;
}
/* ============================================================================================================== */
/* == END FILE ================================================================================================== */
/* ============================================================================================================== */
