```
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
wget https://github.com/tlaplus/CommunityModules/releases/download/202102040137/CommunityModules.jar
java -cp tla2tools.jar:CommunityModules.jar tlc2.TLC BookKeeperProtocol.tla -tool -modelcheck -config BookKeeperProtocol.cfg -workers auto
```
