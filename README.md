# RSASecAnalyzer

Изначальное требование: Система анализа корректности выбранных параметров в криптосистеме RSA.

На вход подается открытый ключ криптосистемы RSA: (e, N), а также timeout в секундах на каждую атаку. При запуске требуется ввести команду:
"/analyze [-e e] [-n N] [-t timeout_in_seconds]"
Или для тестового режима:
"/test [-n system_parameter] [-a attacks list]"

В программе реализованы пять атак на открытый ключ криптосистемы RSA:

Aтакa факторизации модуля (p 1)-методом Полларда
Aтакa факторизации модуля po-методом Полларда
Aтакa восстановления шифр–текста, использующая маленький модуль шифрования
Атака Винера
Атака факторизации, использующая итерацию процесса шифрования.

В консоль выводится отчет о применимости каждой атаки к открытому ключу криптосистемы RSA. 

Атаки прерываются по таймауту.

Тестовый режим сейчас реализован как прогон на реальных данных. 
TODO: нормальный тестовый режим. 
(режим тестирования, который по размеру задачи и списку «применимости» атак, генерирует заведомо слабые секретные ключи, которые могут быть взломаны с использованием списка атак. 

Пример:
Вход: 100, [«(p 1)-метод», «атака Винера»]
Выход: открытый ключ (e,N) и секретный ключ d, где N – имеет размер 200 битов, причём по открытому ключу достаточно легко восстановить секретный ключ, если применить (p 1)-метод или атаку Винера.По размеру задачи генерирует заведомо слабые секретные ключи, которые могут быть взломаны с использованием метода Полига-Хэллмана.)

Важно! Для работы программы необходимо положить файл с факторной базой! Желательно назвать его primes.txt, чтобы программа могла его найти :)
