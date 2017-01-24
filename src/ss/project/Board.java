package ss.project;

import java.util.HashMap;
import java.util.Map;

public class Board {
    public static int MAXFIELD = 3;
    private Map<Field, Mark> fieldMap = new HashMap<Field, Mark>();
    
    public Board() {
        this.reset();
    }
    //@ensures (field.x > MAXFIELD
    //@pure;
    public boolean isField(Field field) {
        return field.x < MAXFIELD || field.y < MAXFIELD || field.z < MAXFIELD;
    }
    
    public void reset() {
        this.fieldMap.clear();
    }
}
