/* ============================================================================================================== */
/* == BEGIN FILE ================================================================================================ */
/* ============================================================================================================== */
/*
 ============================================================================
 Name        : hashtable.c
 Author      : Matthias Thimm
 Version     : 1.0
 Copyright   : GPL3
 Description : A simple hashtable implementation.
 ============================================================================
 */

 /**
 * A simple hash table for strings,
 * collisions are handled by linked lists
 * @author Matthias Thimm
 */
struct StringHashTable{
	struct LinkedList* arr;
	int length;
};

/**
 * Inits the hash table to the given length.
 * @param table
 * @param length
 */
void hash__init(struct StringHashTable* table, int length){
	table->arr = malloc(length * sizeof(struct LinkedList));
	for(int i = 0; i < length; i++)
		llist__init(&table->arr[i]);
	table->length = length;
}

/** Compute the hashcode of the string */
int hash__hashcode(char* string){
	int h = 0;
	int len = strlen(string);
	for(int i = 0; string[i] != '\0'; i++)
		h += string[i] * 127^(len-i);
	return h;
}

/**
 * Inserts the new string and value to the given table.
 * @param table
 * @param string
 * @param value
 */
void hash__insert(struct StringHashTable* table, char* string, int value){
	int idx = hash__hashcode(string) % table->length;
	struct StringValuePair* data = malloc(sizeof(struct StringValuePair));
	data->string = string;
	data->value = value;
	llist__add(&table->arr[idx],data);
}

/**
 * Retrieve the value of the string (or -1 if it is not
 * contained in the given hash table)
 * @param table
 * @param string
 * @return
 */
int hash__get(struct StringHashTable* table, char* string){
	int idx = hash__hashcode(string) % table->length;
	for(struct LinkedListNode* node = table->arr[idx].root; node != 0; node = node->next){
		if(strcmp(((struct StringValuePair*)node->data)->string,string) == 0)
			return ((struct StringValuePair*)node->data)->value;
	}
	return -1;
}

void hash__destroy(struct StringHashTable* table){
	llist__destroy(table->arr);
	free(table);
}

/* ============================================================================================================== */
/* == END FILE ================================================================================================== */
/* ============================================================================================================== */
