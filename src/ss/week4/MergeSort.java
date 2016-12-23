package ss.week4;

import java.util.*;

public class MergeSort {
    public static <Elem extends Comparable<Elem>>
           List<Elem> mergesort(List<Elem> list) {
                if (list.size() < 2) {
                    return list;
                }
                int mid = list.size() / 2;
                
                List<Elem> left = new ArrayList<>(list.subList(0, mid));
                List<Elem> right = new ArrayList<>(list.subList(mid, list.size()));
                
                left = mergesort(left);
                right = mergesort(right);
                
                return merge(left,right);
    	// TODO: implement, see exercise P-4.16
    }
    private static <Elem extends Comparable<Elem>> List<Elem> merge(List<Elem> left,List<Elem> right) {
        List<Elem> result = new ArrayList<>();
        while (left.size() > 0 && right.size() > 0) {
            if (left.get(0).compareTo(right.get(0)) < 0 ) {
                result.add(left.get(0));
                left.remove(0);
            }
            else {
                result.add(right.get(0));
                right.remove(0);
            }
        }
        while (!left.isEmpty()) {
            result.add(left.get(0));
            left.remove(0);
        }
        while (!right.isEmpty()) {
            result.add(right.get(0));
            right.remove(0);
        }
        return result;
    }
}
