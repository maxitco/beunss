package ss.week5;

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
    public static <K, V> boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
        
        
        
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
        //creating variables of the function
        Map<V, Set<K>> mapInverse = new HashMap<V, Set<K>>();
        //array list of sets, wonderful
        List<Set<K>> setK = new ArrayList<Set<K>>();
        
        //while loop setup
        Iterator<Map.Entry<K, V>> loopEntries = map.entrySet().iterator(); //iterator over all entries of the map        
        int index = 0; //index for sets
        
        //loop over all entries
        while (loopEntries.hasNext()) {
            //add a new set or the current entry
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
            //only if there is an entry the index is increased since if there is counter < 0 then the Set on the current index is not used in mapInverse            
            if (counter > 0) {
                mapInverse.put(entry.getValue(), setK.get(index));
                index = index + 1;
            }
        }
        return mapInverse;        
    }
    
    public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        assert(isOneOnOne(map));
        assert(isSurjectiveOnRange(map, (Set) map.values()));
        Map<V, K> mapInverse = new HashMap<V, K>();
                
        //Iterator using while loop
        Iterator<Map.Entry<K, V>> loopEntries = map.entrySet().iterator();        
                
        //Pass all entries
        while (loopEntries.hasNext()) {
            Map.Entry<K, V> entry = loopEntries.next();
            mapInverse.put(entry.getValue(), entry.getKey());            
        }        
        return mapInverse;        
    }
    
    public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        Iterator<V> iterator_V = f.values().iterator(); 
        
        while(iterator_V.hasNext()) {
            V currentV = iterator_V.next();
            Iterator<K> iterator_K = (Iterator<K>) g.keySet().iterator();
            boolean gotCha = false;
            while(iterator_K.hasNext() && !gotCha) {
                K currentK = iterator_K.next(); 
                if(currentK.equals(currentV)) {
                    gotCha = true;                    
                }
            }
            
            if (gotCha == false) {
                return gotCha;
            }
            
        }
        return true;
    }
    public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        if(compatible(f,g)) {
            Map<K, W> h = new HashMap<K,W>();
            
            Iterator<Map.Entry<K, V>> entriesF = f.entrySet().iterator(); 
            while(entriesF.hasNext()) {
                Map.Entry<K, V> entryF = entriesF.next();
                
                Iterator<Map.Entry<V,W>> entriesG = g.entrySet().iterator();
                while(entriesG.hasNext()) {
                    Map.Entry<V, W> entryG = entriesG.next(); 
                    if (entryF.getValue().equals(entryG.getKey())) {
                        h.put(entryF.getKey(), entryG.getValue());                    
                    }
                }                
                      
            }
            return h;
        }
                 
        else {
            return null;
        }
    }
}
