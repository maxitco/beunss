package ss.week4;

import java.util.*;

public class Exercises {
    public static int countNegativeNumbers(int[] arr) {
        int negcount = 0;
        for (int i = 0; i < arr.length; i++)
        {
            if (arr[i] < 0)
            {
                negcount++;
            }
        }
        return negcount;
    }

    public static void reverseArray(int[] ints) {
        int half = ints.length / 2;
        int tmp;
        for (int i = 0; i < half; i++) {
            int lastpos = ints.length - 1 - i;
            tmp = ints[i];
            ints[i] = ints[lastpos];
            ints[lastpos] = tmp;
        }
        
    }

    class SimpleList {
        public class Element {}

        public class Node {
            public Node next;
            public Element element;
        }

        private Node first;

        private Node find(Element element) {
            Node p = first;
            if (p == null) {
                return null;
            }
            while (p.next != null && !p.next.element.equals(element)) {
                p = p.next;
            }
            if (p.next == null) {
                return null;
            } else {
                return p;
            }
        }

        public void remove(Element element) {
            Node p = find(element);
            if (p != null) {
                p.next = p.next.next;
            }
        }
    }
}
