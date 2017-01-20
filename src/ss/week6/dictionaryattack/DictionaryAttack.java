package ss.week6.dictionaryattack;

import java.util.Map;
import java.util.HashMap;
import java.io.*;
import java.lang.String;
import org.apache.commons.codec.digest.DigestUtils;



public class DictionaryAttack {
	private Map<String, String> passwordMap = new HashMap<String, String>();
	private Map<String, String> hashDictionary = new HashMap<String, String>();

	/**
	 * Reads a password file. Each line of the password file has the form:
	 * username: encodedpassword
	 * 
	 * After calling this method, the passwordMap class variable should be
	 * filled withthe content of the file. The key for the map should be
	 * the username, and the password hash should be the content.
	 * @param filename
	 */
	public void readPasswords(String filename) throws FileNotFoundException, IOException {
	        BufferedReader input =  new BufferedReader(new FileReader(filename));
	        try {
	            String line = null;
	            while (( line = input.readLine()) != null){
	                String[] parts = line.split(": ");
	                this.passwordMap.put(parts[0], parts[1]);
	            }
	        }
	        finally {
	            input.close();
	        }
	    
	}

	/**
	 * Given a password, return the MD5 hash of a password. The resulting
	 * hash (or sometimes called digest) should be hex-encoded in a String.
	 * @param password
	 * @return
	 */
	public String getPasswordHash(String password) throws IOException {
	    return DigestUtils.md5Hex(password);	    
	}
	/**
	 * Checks the password for the user the password list. If the user
	 * does not exist, returns false.
	 * @param user
	 * @param password
	 * @return whether the password for that user was correct.
	 */
	public boolean checkPassword(String user, String password) {
	    try {
        if (this.passwordMap.containsKey(user)) {
            return this.passwordMap.get(user).equals(this.getPasswordHash(password));
        }
	    }
	    catch (IOException ex) {
	        
	    }
		return false;
	}

	/**
	 * Reads a dictionary from file (one line per word) and use it to add
	 * entries to a dictionary that maps password hashes (hex-encoded) to
     * the original password.
	 * @param filename filename of the dictionary.
	 */
    	public void addToHashDictionary(String filename) throws IOException {
    	    BufferedReader input =  new BufferedReader(new FileReader(filename));
            try {
                String line = null;
                while (( line = input.readLine()) != null){
                    this.hashDictionary.put(this.getPasswordHash(line), line);
                }
            }
            finally {
                input.close();
            }
    }
	/**
	 * Do the dictionary attack.
	 */
	public void doDictionaryAttack() {
	    try {
	        this.addToHashDictionary("./10_million_password_list_top_10000.txt");
	        this.readPasswords("./bigsimplecorp_pw_hashes.txt");
	        int count = 0;
	        int found = 0;
	        for (Map.Entry<String, String> entry : this.passwordMap.entrySet()) {
	            count++;
	            if (this.hashDictionary.containsKey(entry.getValue())) {
	                String pw = this.hashDictionary.get(entry.getValue());
	                if (this.checkPassword(entry.getKey(), pw)) {
	                    found++;
	                    System.out.println(entry.getKey() + ": " + pw);
	                }
	            }
	        }
	        System.out.println(found + "/" + count);
	        
	    }
	    catch (IOException ex0) {
	        System.err.println("unable to open file");
	    }
		
	}
	public static void main(String[] args) {
		DictionaryAttack da = new DictionaryAttack();
		// To implement
		da.doDictionaryAttack();
	}

}
//6.23
// 26^4
