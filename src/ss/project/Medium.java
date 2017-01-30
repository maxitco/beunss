package ss.project;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

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
        
        for (Field field : moves) {
            Board test = board.copy();
            test.setField(field, m);
            if (test.isWinner(m)) {
                result.put(field, new Integer(25));
            }
            else if (test.isWinner(m.other())) {
                result.put(field, new Integer(20));
            }
            else {
            	result.put(field, new Integer(countSurroundings(field, board, m)));
            }
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
    					if (board.getMark(neighbour).equals(m)) {
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
    	System.out.println(result);
    	return result;
    }

}
