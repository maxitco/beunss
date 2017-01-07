package ss.week4;

import ss.week4.LinkedList.Node;

public class LinkedList<E> {

    private /*@ spec_public @*/ int size;
    private Node first;

    //@ ensures \result.size == 0;
    public LinkedList() {
        size = 0;
        first = null;
    }

    public void add(int index, E element) {
        Node newNode = new Node(element);
        if (index == 0) {
            newNode.next = first;
            first = newNode;
        } else {
            Node p = getNode(index - 1);
            newNode.next = p.next;
            p.next = newNode;
        }
        size = size + 1;
    }

    //@ ensures this.size == \old(size) - 1;
    public void remove(E element) {
        // TODO: implement, see exercise P-4.18
        if(getNode(0).getElement().equals(element)) {
            first = getNode(1);
        } else {
        findBefore(element).next = findBefore(element).next.next;
        }
        size = size - 1;         
    }

    public Node findBefore(E element) {
        Node result = null;
        int i = 1;
        while (i < (size) && result == null) {
            
            if (getNode(i).getElement() != null && getNode(i).getElement().equals(element)) {
                result = getNode(i - 1);
            }            
            
            i++;            
        }
        return result;      
    }

    //@ requires 0 <= index && index < this.size();
    public E get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    //@ requires 0 <= i && i < this.size();
    private /*@ pure @*/ Node getNode(int i) {
        Node p = first;
        int pos = 0;
        while (pos != i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    //@ ensures \result >= 0;
    public /*@ pure @*/ int size() {
        return size;
    }

    public class Node {
        private E element;
        public Node next;

        public Node(E element) {
            this.element = element;
            this.next = null;
        }

        public E getElement() {
            return element;
        }
    }
}
