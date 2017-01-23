package ss.project;

import java.util.HashMap;
import java.util.Map;

public class Board {
    public static int MAXFIELD = 3;
    private Map<Field, Mark> fieldMap = new HashMap<Field, Mark>();
    
    public Board() {
        this.reset();
    }
    
    public void reset() {
        this.fieldMap.clear();
    }
}
