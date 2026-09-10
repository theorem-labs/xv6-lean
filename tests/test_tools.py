"""Fail-closed tests for the untrusted input importer."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("images", ROOT / "tools/images.py")
images = importlib.util.module_from_spec(spec)
spec.loader.exec_module(images)


def chunk(i, value):
    return f'Definition test_chunk{i} : PrimString.string := "{value}"%pstring.'


class ImageImporter(unittest.TestCase):
    def test_preserves_bytes_and_order(self):
        self.assertEqual(images.extract(chunk(0, "00ff") + "\n" + chunk(1, "ab"), "test"), bytes([0, 255, 171]))

    def test_rejects_missing_duplicated_or_out_of_order_chunks(self):
        for indexes in [(1,), (0, 2), (0, 0), (1, 0)]:
            with self.subTest(indexes=indexes), self.assertRaises(ValueError):
                images.extract("\n".join(chunk(i, "00") for i in indexes), "test")

    def test_rejects_odd_hex(self):
        with self.assertRaises(ValueError):
            images.extract(chunk(0, "0"), "test")

    def test_rejects_malformed_extra_chunk(self):
        with self.assertRaises(ValueError):
            images.extract(chunk(0, "00") + "\n" + chunk(1, "zz"), "test")

    def test_rejects_absent_data(self):
        with self.assertRaises(ValueError):
            images.extract("", "test")


if __name__ == "__main__":
    unittest.main()
