package ss.project;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Collections; 
import java.util.Iterator;

public class Medium implements Difficulty {

    @Override
    public String getName() {
        return "medium";
    }

    @Override
    public Field determineMove(Board board, Mark m) {
    	Map<Field, Integer> result = new HashMap<Field, Integer>();
        ArrayList<Field> moves = new ArrayList<Field>();
        for (int x = 0; x <= Board.MAXFIELD; x++) {
            for (int y = 0; y <= Board.MAXFIELD; y++) {
                Field empty = board.getEmptyField(x, y);
                if (empty != null) {
                    moves.add(empty);
                }
            }
        }
        System.out.println(moves.size());
        for (Field field : moves) {
            Board test = board.copy();
            Board test2 = board.copy();
            test.setField(field, m);
            test2.setField(field, m.other());
            if (test.isWinner(m)) {
                result.put(field, new Integer(50));
            }
            else if (test2.isWinner(m.other())) {
                result.put(field, new Integer(40));
            }
            else {
            	result.put(field, new Integer(countSurroundings(field, board, m)));
            }
        }
        int maxValue = Collections.max(result.values());
        System.out.println(maxValue);
        Iterator<Map.Entry<Field, Integer>> it = result.entrySet().iterator();
        while (it.hasNext()) {
        	Map.Entry<Field,Integer> item = it.next();
        	if (item.getValue().intValue() < maxValue) {
        		it.remove();
        	}
        }
        it = result.entrySet().iterator();
        int next = (int) (Math.random() * new Double(result.size()));
        int count = 0;
        while (it.hasNext()) {
        	Map.Entry<Field,Integer> item = it.next();
        	if (count == next) {
        		System.out.println(m.toString() + " chose " + item.getKey().toString());
        		return item.getKey();
        	}
        	count++;
        }
        
        return null;
    }
    
    public int countSurroundings(Field field, Board board, Mark m) {
    	int result = 0;
    	for (int z = -1; z <= 0; z++) {
    		for (int i = -1; i <= 1; i++) {
    			for (int a = -1; a <= 1; a++) {
    				Field neighbour = board.walkField(field, i, a, z);
    				//next to field of same color
    				if (neighbour != null) {
    					Mark nextmark = board.getMark(neighbour);
    					if (nextmark != null && nextmark.equals(m)) {
        					result++;
    					}
    				}
    				//next to boundary
    				else if (neighbour == null) {
    					result++;
    				}
    			}
    		}
    	}
    	return result;
    }

}
