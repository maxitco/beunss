package ss.week4;

import ss.week4.DoublyLinkedList.Node;

public class DoublyLinkedList<E> {

    private /*@ spec_public @*/ int size;
    private Node head;

    //@ ensures this.size == 0;
    public DoublyLinkedList() {
        size = 0;
        head = new Node(null);
        head.next = head;
        head.previous = head;
    }

    
    //@ requires 0 <= index && index <= this.size;
    //@ ensures this.size == \old(size) + 1;
    //@ ensures this.getNode(index).equals(element);
    public void add(int index, E element) {
        //assert 0 <= index;
        //assert index <= this.size;
        
        //increase size
        size = size + 1;
        
        //create new node to add        
        Node adder = new Node(element);
        
        //only case where there is not element before adder
        if (index == 0) {
            if(size == 0) {
                head = adder;
                head.previous = head;
                head.next = head;
            } else {
                adder.previous = head.previous;
                adder.next = head;
                head.previous.next = adder;
                head.previous = adder;   
                head = adder;
            }
        } else {
          
            Node searcher = getNode(index);
            //set previous node to the one whose index is 1 lower than that of adder.
            adder.next = searcher;
            adder.previous = searcher.previous;
            searcher.previous = adder;
            adder.previous.next = adder;          
        }
    }

    //@ requires 0 <= index && index < this.size;
    //@ ensures this.size == \old(size) - 1;
    public void remove(int index) {
        Node searcher = head;
        
        if (index == 0) {
            head = head.next;
            head.previous = head;
            
        } else{
            searcher = getNode(index - 1);
            searcher.next.previous = searcher.previous;
            searcher.previous.next = searcher.next;                        
        }
        size = size - 1;
    }

    //@ requires 0 <= index && index < this.size;
    /*@ pure */ public E get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    /**
     * The node containing the element with the specified index.
     * The head node if the specified index is -1.
     */
    //@ requires 0 <= i && i < this.size;
    //@ pure
    public Node getNode(int i) {
        Node p = head;
        int pos = 0;
        while (pos < i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    public int size() {
        return this.size;
    }
    public class Node {
        public Node(E element) {
            this.element = element;
            this.next = null;
            this.previous = null;            
        }

        private E element;
        public Node next;
        public Node previous;

        public E getElement() {
            return element;
        }
    }
}
