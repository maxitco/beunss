package ss.week5;
//nudan
import java.security.KeyStore.Entry;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;


public class MapUtil {
        
    //@ requires map != null;
    //@ ensures \result == true || \result == false;
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        //while loop setup
        boolean go_flag = true;
        Iterator<V> iterator_V = map.values().iterator();
        
        //iterate through all values
        while(iterator_V.hasNext() && go_flag) {
            V value = iterator_V.next();
            
            //for loop setup
            int keyNo = 0;
            
            //check how often the values are present            
            for (Map.Entry<K, V> entry : map.entrySet()) {
                if (value.equals(entry.getValue())) {
                    keyNo = keyNo + 1;
                }
            }
            
            //each value should only be found once since each entry indicates one key - value coupling
            if(keyNo != 1) {
                go_flag = false;
            }            
        }
        return go_flag;
    }
    
    //@ requires map != null;
    //@ ensures \result == true || \result == false;
    public static <K, V> 
           boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
        // TODO: implement, see exercise P-5.2
        
        
        //while loop setup
        boolean go_flag = true;
        Iterator<V> iterator_V = range.iterator();
        
        //iterate through all values
        while(iterator_V.hasNext() && go_flag) {
            V value = iterator_V.next();
            
            //for loop setup
            int keyNo = 0;
            
            //check how often the values are present            
            for (Map.Entry<K, V> entry : map.entrySet()) {
                if (value.equals(entry.getValue())) {
                    keyNo = keyNo + 1;
                }
            }
            
            //each value should only be found once since each entry indicates one key - value coupling
            if(keyNo < 1) {
                go_flag = false;
            }            
        }
        return go_flag;
    }

    public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
        // TODO: implement, see exercise P-5.3
        Map<V, Set<K>> mapInverse = new HashMap<V, Set<K>>();
        List<Set<K>> setK = new ArrayList<Set<K>>();
        
        //Iterator using while loop
        Iterator<Map.Entry<K, V>> loopEntries = map.entrySet().iterator();        
        
        int index = 0; //index for sets
        
        //Pass all entries
        while (loopEntries.hasNext()) {
            
            setK.add(index, new HashSet<K>());
            
            Map.Entry<K, V> entry = loopEntries.next();
            
            //Iterator 2 using while loop
            Iterator<Map.Entry<K, V>> loopEntries2 = map.entrySet().iterator();
            int counter = 0;
            
            //pass all entries again to check for duplicate values            
            while (!map.isEmpty() && loopEntries2.hasNext()) {
                Map.Entry<K, V> entry2 = loopEntries2.next();
                
                //check for same value
                if (entry.getValue().equals(entry2.getValue())) {
                    counter = counter + 1; //counts how many entries have the same value
                    
                    setK.get(index).add(entry2.getKey()); //add key to the set of keys
                    map.remove(entry2); //remove duplicate entry from map such that it is not used multiple times
                }                
            }
            //if a there is at least one entry with the same value then add it to the mapinverse
            
            if (counter > 0) {
                mapInverse.put(entry.getValue(), setK.get(index));
                index = index + 1;
            }
        }
        
        return mapInverse;        
    }
    
    public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        // TODO: implement, see exercise P-5.3
        return null;
    }
    public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.4
        return false;
    }
    public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.5
        return null;
    }
}
